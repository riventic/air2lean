#!/usr/bin/env python3
"""Check selected project AIR with a versioned diagnostic producer; emit no Lean."""
import argparse
import json
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import tempfile

import project

PROTOCOL_HEAD = '6b6a20c329ee2639c39b09e1e7b312c6722bfd31'
KIND = 'air2lean-check-diagnostics'
CODES = frozenset('CLI_ARGUMENTS INPUT_READ INPUT_LIMIT JSON_SYNTAX AIR_DECODE EXPORTER_UNSUPPORTED OPTIMIZED_UNSUPPORTED CANONICAL_FAILURE NORMALIZATION_FAILURE STRUCTURE_FAILURE TYPE_FAILURE GLOBAL_FAILURE MEMORY_FAILURE INSTRUCTION_FAILURE CONSTANT_FAILURE SIGNATURE_FAILURE MODEL_FAILURE PROGRAM_FAILURE PROFILE_FAILURE DUPLICATE_FUNCTION CALLEE_MISSING CALLEE_BLOCKED CALLEE_AMBIGUOUS PREREQUISITE_SKIPPED VOLATILE_ACCESS PACKED_LAYOUT PADDED_ATOMIC ASM_VOLATILE_EFFECT EMITTER_PLACEHOLDER'.split())
PHASES = frozenset('cli input decode canonicalize normalize check program profile'.split())
CATEGORIES = frozenset('malformed_input unsupported_semantics validation_failure resource_limit io_failure skipped_prerequisite'.split())
DEPENDENCIES = 'selected_normalized_direct_calls_and_spawn_workers'
PRODUCER_SCHEMA = 2
REPORT_KEYS = ('schema', 'kind', 'status', 'complete', 'truncated', 'diagnostic_limit',
               'diagnostics_observed', 'diagnostic_payload_bytes', 'caps', 'capped_units', 'diagnostics', 'files',
               'scope', 'proof_status', 'runtime_outcomes', 'dependency_completeness', 'source_correspondence')
DIAGNOSTIC_KEYS = ('code', 'phase', 'category', 'message', 'message_truncated', 'file', 'function',
                   'anchor', 'source_span', 'source_span_status', 'dependency_chain',
                   'dependency_scope', 'prerequisites', 'first_error_in_unit', 'fatal')
SPAN_KEYS = ('file', 'module', 'line', 'column')
# Fixed producer bounds; the two counts are requested per invocation.
CAPS = {'payload_bytes': 1024 * 1024, 'message_chars': 2048, 'files': 256,
        'input_bytes': 64 * 1024 * 1024, 'function_name_chars': 1024, 'dependency_chain_names': 257}


def demand(ok, message):
    if not ok:
        raise project.Invalid(message)


def natural(value, maximum=None):
    return type(value) is int and value >= 0 and (maximum is None or value <= maximum)


def text(value, nullable=False):
    return (nullable and value is None) or (isinstance(value, str) and
        all(not 0xD800 <= ord(c) <= 0xDFFF for c in value))


def lean_compact_size(value):
    """UTF-8 bytes of Lean 4.34 Json.compress for schema-1 typed JSON values.

    Printer.lean escapeAux uses short escapes only for quote, backslash, LF and CR;
    all other controls use six-byte Unicode escapes. Work iterators keep depth bounded
    without materializing an encoded copy or rewriting literal backslash sequences.
    """
    def string_size(value):
        demand(isinstance(value, str), 'JSON object key is not a string')
        size = 2
        for char in value:
            code = ord(char)
            demand(not 0xD800 <= code <= 0xDFFF, 'invalid Unicode scalar in receipt')
            if char in ('"', '\\', '\n', '\r'):
                size += 2
            elif code < 0x20:
                size += 6
            else:
                size += 1 if code < 0x80 else 2 if code < 0x800 else 3 if code < 0x10000 else 4
        return size
    total = 0
    pending = [iter((value,))]
    while pending:
        try:
            item = next(pending[-1])
        except StopIteration:
            pending.pop()
            continue
        if item is None:
            total += 4
        elif type(item) is bool:
            total += 4 if item else 5
        elif type(item) is int:
            demand(item >= 0, 'producer protocol number is not Nat')
            total += len(str(item))
        elif isinstance(item, str):
            total += string_size(item)
        elif isinstance(item, list):
            total += 2 + max(0, len(item) - 1)
            pending.append(iter(item))
        elif isinstance(item, dict):
            total += 2 + max(0, len(item) - 1) + len(item)
            total += sum(string_size(key) for key in item)
            pending.append(iter(item.values()))
        else:
            raise project.Invalid('unsupported producer protocol value')
        demand(len(pending) <= project.LIMITS['max_json_depth'] + 1, 'producer value exceeds JSON depth')
    return total


def valid_span(d):
    """Exporter provenance only: a module-relative file, absolute line, optional column."""
    span, status = d['source_span'], d['source_span_status']
    if span is None:
        return status == 'unavailable_in_AIR'
    project.obj(span, SPAN_KEYS)
    return (status in ('statement', 'declaration') and text(span['file']) and text(span['module']) and
            0 < len(span['file']) <= 4096 and 0 < len(span['module']) <= 1024 and
            natural(span['line']) and span['line'] >= 1 and
            (span['column'] is None if status == 'declaration' else
             span['column'] is None or (natural(span['column']) and span['column'] >= 1)))


def validate_receipt(raw, returncode, mapping, air_dir, limit, unit_limit=64):
    """Reject unknown schema/vocabulary and inconsistent evidence, without parsing messages."""
    demand(len(raw) <= project.LIMITS['max_output_bytes'], 'diagnostic receipt exceeds byte bound')
    receipt = project.bounded_json(raw, project.LIMITS)
    project.obj(receipt, REPORT_KEYS)
    demand(type(receipt['schema']) is int and receipt['schema'] == PRODUCER_SCHEMA and receipt['kind'] == KIND,
           'unsupported diagnostic protocol')
    demand(receipt['status'] in ('checked', 'rejected') and
           returncode == (0 if receipt['status'] == 'checked' else 1), 'diagnostic exit/status mismatch')
    for key in ('complete', 'truncated'):
        demand(type(receipt[key]) is bool, f'invalid {key}')
    demand(type(receipt['diagnostic_limit']) is int and receipt['diagnostic_limit'] == limit,
           'diagnostic limit mismatch')
    demand(natural(receipt['diagnostics_observed']) and natural(receipt['diagnostic_payload_bytes'], 1024 * 1024),
           'invalid diagnostic counters')
    project.obj(receipt['caps'], ('diagnostics', 'diagnostics_per_unit') + tuple(CAPS))
    demand(receipt['caps'] == dict(CAPS, diagnostics=limit, diagnostics_per_unit=unit_limit),
           'diagnostic caps mismatch')
    demand(receipt['proof_status'] == 'not_run' and receipt['runtime_outcomes'] == 'not_observed' and
           receipt['source_correspondence'] == 'not_attested', 'inflated diagnostic evidence')
    demand(receipt['scope'] == 'selected AIR validation; first error within opaque prerequisite units' and
           receipt['dependency_completeness'] == 'not_attested; direct normalized calls and explicit spawn workers only',
           'unknown diagnostic scope')
    diagnostics = receipt['diagnostics']
    demand(isinstance(diagnostics, list) and len(diagnostics) <= limit and
           receipt['diagnostics_observed'] >= len(diagnostics), 'invalid diagnostic count')
    def known_file(value, directory=False):
        return value is None or value in mapping or (directory and value == str(air_dir))
    for d in diagnostics:
        project.obj(d, DIAGNOSTIC_KEYS)
        demand(d['code'] in CODES and d['phase'] in PHASES and d['category'] in CATEGORIES,
               'unknown diagnostic vocabulary')
        demand(text(d['message']) and len(d['message']) <= 2048 and text(d['function'], True),
               'invalid diagnostic text')
        demand(type(d['message_truncated']) is bool and type(d['first_error_in_unit']) is bool,
               'invalid diagnostic flags')
        demand(known_file(d['file'], True), 'unknown diagnostic file')
        project.obj(d['anchor'], ('id_space', 'instruction', 'type', 'global', 'nearest_dbg_line'))
        demand(d['anchor']['id_space'] in ('unavailable', 'exported', 'canonical'), 'unknown ID space')
        for key in ('instruction', 'type', 'global', 'nearest_dbg_line'):
            demand(d['anchor'][key] is None or natural(d['anchor'][key]), 'invalid diagnostic anchor')
        demand(type(d['fatal']) is bool, 'invalid diagnostic flags')
        demand(valid_span(d), 'invalid source span')
        demand(d['dependency_scope'] == DEPENDENCIES, 'unknown dependency scope')
        for key in ('dependency_chain', 'prerequisites'):
            demand(isinstance(d[key], list) and all(text(v) for v in d[key]), 'invalid diagnostic context')
        demand(len(d['dependency_chain']) <= 257, 'dependency chain exceeds producer bound')
    retained = {}
    for d in diagnostics:
        retained[d['file'] or ''] = retained.get(d['file'] or '', 0) + 1
    demand(all(count <= unit_limit for count in retained.values()), 'per-unit diagnostic cap exceeded')
    capped = receipt['capped_units']
    demand(isinstance(capped, list) and len(capped) <= len(mapping) + 2, 'invalid capped units')
    for item in capped:
        project.obj(item, ('file', 'dropped'))
        demand((item['file'] == '' or known_file(item['file'], True)) and natural(item['dropped']) and
               item['dropped'] >= 1, 'invalid capped unit')
    demand([item['file'] for item in capped] == sorted({item['file'] for item in capped}),
           'unsorted or duplicate capped units')
    dropped = sum(item['dropped'] for item in capped)
    demand(receipt['diagnostics_observed'] == len(diagnostics) + dropped, 'unreported dropped diagnostics')
    demand(bool(capped) == receipt['truncated'], 'truncation and capped units disagree')
    if receipt['truncated'] or any(d['first_error_in_unit'] for d in diagnostics):
        demand(not receipt['complete'], 'hidden diagnostic incompleteness')
    payload = sum(lean_compact_size(d) for d in diagnostics)
    demand(payload <= 1024 * 1024 and receipt['diagnostic_payload_bytes'] == payload,
           'invalid retained diagnostic payload')
    if receipt['truncated']:
        demand(receipt['diagnostics_observed'] > len(diagnostics), 'truncation lacks dropped diagnostic')
    else:
        demand(receipt['diagnostics_observed'] == len(diagnostics), 'unreported diagnostic additions')
    files = receipt['files']
    demand(isinstance(files, list) and len(files) <= 256, 'invalid file inventory')
    names = []
    for item in files:
        project.obj(item, ('file', 'function', 'normalized', 'structure_valid', 'local_check'))
        demand(item['file'] in mapping and text(item['function'], True), 'unknown file result')
        demand(type(item['normalized']) is bool and type(item['structure_valid']) is bool and
               item['local_check'] in ('passed', 'blocked_or_rejected'), 'invalid local check')
        demand(not item['normalized'] or isinstance(item['function'], str), 'normalized function lacks identity')
        demand(not item['structure_valid'] or item['normalized'], 'structure without normalized function')
        demand(item['local_check'] != 'passed' or item['structure_valid'], 'local success without structure')
        names.append(item['file'])
    directory_failure = (not names and receipt['status'] == 'rejected' and not receipt['complete'] and
        any(d['code'] in ('INPUT_READ', 'CLI_ARGUMENTS') and d['file'] in (None, str(air_dir))
            for d in diagnostics))
    demand(names == sorted(mapping)[:256] or directory_failure,
           'incomplete or reordered diagnostic file inventory')
    if receipt['status'] == 'checked':
        demand(receipt['complete'] and not receipt['truncated'] and not diagnostics and
               bool(files) and len(mapping) <= 256 and all(f['local_check'] == 'passed' for f in files),
               'inconsistent successful check')
    else:
        demand(receipt['truncated'] or any(d['category'] != 'skipped_prerequisite' for d in diagnostics),
               'rejection lacks blocker')
    # All validation and raw-byte counters precede mapping this locally owned receipt.
    for d in receipt['diagnostics']:
        d['file'] = mapping.get(d['file'], '${SELECTED_AIR}' if d['file'] == str(air_dir) else None)
        d['message'] = d['message'].replace(str(air_dir), '${SELECTED_AIR}')
    for item in receipt['files']:
        item['file'] = mapping[item['file']]
    for item in receipt['capped_units']:
        item['file'] = mapping.get(item['file'], '${SELECTED_AIR}' if item['file'] == str(air_dir) else None)
    return receipt


def invoke(argv, cwd, limits):
    """Keep separate raw streams and diagnostic execution codes."""
    result = project._run_bounded(argv, cwd, limits, merged=False)
    if result['failure']:
        result['failure'] = {'timeout': 'CHECK_TIMEOUT', 'output_limit': 'CHECK_OUTPUT_LIMIT',
                             'descendants': 'CHECK_DESCENDANTS'}[result['failure']]
    return result


def issue(code, stage, message, path=None):
    return {'code': code, 'stage': stage, 'message': str(message), 'path': path,
            'source_span': None, 'source_span_status': 'unavailable_in_AIR'}


def preflight_air(boundaries):
    """Classify typed boundaries observed during collection, without parsing message text."""
    issues = {}
    for name, boundary in boundaries.items():
        local = issues[name] = []
        if boundary.syntax_error is not None:
            local.append(issue('AIR_SYNTAX', 'import', boundary.syntax_error, name))
        elif not boundary.schema_valid:
            local.append(issue('AIR_SCHEMA', 'schema', 'unsupported or malformed AIR schema', name))
        else:
            if boundary.version_endian_mismatch:
                local.append(issue('AIR_PROFILE', 'profile', 'AIR version/endian differs from manifest profile', name))
            if boundary.profile_error is not None:
                local.append(issue('AIR_PROFILE', 'profile', boundary.profile_error, name))
    return issues


def check_project(manifest_path, translator, limit, runner=invoke, unit_limit=64):
    boundaries = {}
    manifest, limits, data, evidence = project.collect(manifest_path, air_boundaries=boundaries)
    translator = translator.resolve(strict=True)
    tool_hash, tool_bytes = project.hash_bounded(translator, 256 * 1024 * 1024)
    envelope = {'schema': 1, 'kind': 'air2lean-project-diagnostics', 'evidence': evidence,
                'translator': {'path': str(translator), 'sha256': tool_hash, 'bytes': tool_bytes},
                'producer_protocol': {'schema': PRODUCER_SCHEMA, 'kind': KIND, 'reference_revision': PROTOCOL_HEAD,
                                      'qualification': 'not_attested_by_adapter'},
                'root_checks': [], 'complete': True, 'truncated': False,
                'proof_status': 'not_run', 'runtime_outcomes': 'not_observed', 'source_correspondence': 'not_attested'}
    preflight = preflight_air(boundaries)
    shared_names = set(manifest['source_closure']) | {manifest['profile']}
    for names in manifest['components'].values():
        shared_names.update(names)
    input_failures = {d['path']: d['message'] for d in evidence['diagnostics'] if d['code'] == 'INPUT_FILE'}
    missing_roots = {d['root']: d['message'] for d in evidence['diagnostics'] if d['code'] == 'ROOT_NOT_PRESENT'}
    shared_issues = [issue('PROJECT_IMPORT', 'import', message, name)
                     for name, message in input_failures.items() if name in shared_names]
    if evidence['profile'] is None:
        shared_issues.append(issue('PROJECT_PROFILE', 'profile', 'validated manifest profile unavailable', manifest['profile']))
    consumed = 0
    with tempfile.TemporaryDirectory(prefix='air2lean-project-diagnostics-') as temporary:
        for root in manifest['roots']:
            local = list(shared_issues)
            for name in root['air']:
                if name not in data:
                    local.append(issue('AIR_UNAVAILABLE', 'import', 'selected AIR bytes unavailable', name))
                else:
                    local.extend(preflight[name])
            if root['id'] in missing_roots:
                local.append(issue('PROJECT_ROOT', 'import', missing_roots[root['id']]))
            for name in root['contracts']:
                if name in input_failures:
                    local.append(issue('CONTRACT_IMPORT', 'import', input_failures[name], name))
            record = {'root': root['id'], 'status': 'not_run', 'complete': False, 'truncated': False,
                      'preflight': local, 'path_map': [], 'producer': None, 'execution': None,
                      'producer_counters_basis': 'raw_stdout_before_path_mapping'}
            envelope['root_checks'].append(record)
            # Missing bytes cannot be replaced or passed off as a checked closure. Syntax
            # errors in readable bytes still pass through to independent producer units.
            if evidence['profile'] is None or any(name not in data for name in root['air']):
                record['status'] = 'blocked'
                continue
            remaining = limits['max_total_output_bytes'] - consumed
            if remaining <= 0:
                record['preflight'].append(issue('PROJECT_CHECK_LIMIT', 'execution', 'project receipt budget exhausted'))
                record['truncated'] = True
                continue
            rootdir = Path(temporary) / root['id']
            rootdir.mkdir()
            air_dir = rootdir / 'air'
            air_dir.mkdir()
            mapping = {}
            for index, name in enumerate(root['air']):
                staged = air_dir / f'{index:06d}.json'
                staged.write_bytes(data[name])
                mapping[str(staged)] = name
                record['path_map'].append({'staged': staged.name, 'path': name,
                                           'sha256': evidence['files']['input/' + name]['sha256']})
            argv = [str(translator), '--diagnostics-json', str(air_dir), '--profile', evidence['profile']['name'],
                    '--diagnostic-limit', str(limit), '--unit-diagnostic-limit', str(unit_limit),
                    '--spawn-policy', project.spawn_policy(manifest)]
            try:
                result = runner(argv, rootdir, dict(limits, max_output_bytes=min(limits['max_output_bytes'], remaining)))
                consumed += len(result['stdout']) + len(result['stderr'])
                record['execution'] = {'argv': [arg.replace(str(air_dir), '${SELECTED_AIR}') for arg in argv],
                    'returncode': result['returncode'], 'stdout_sha256': project.digest(result['stdout']),
                    'stdout_bytes': len(result['stdout']), 'stderr_sha256': project.digest(result['stderr']),
                    'stderr_bytes': len(result['stderr'])}
                if result['failure']:
                    record['status'] = 'error'
                    record['preflight'].append(issue(result['failure'], 'execution', 'producer invocation did not complete within controls'))
                else:
                    try:
                        demand(not result['stderr'], 'diagnostic producer wrote unexpected stderr')
                        parsed = validate_receipt(result['stdout'], result['returncode'], mapping, air_dir, limit, unit_limit)
                        record['producer'] = parsed
                        record['status'] = 'rejected' if local or parsed['status'] == 'rejected' else 'checked'
                        record['complete'] = parsed['complete']
                        record['truncated'] = parsed['truncated']
                    except (ValueError, UnicodeError, RecursionError, TypeError) as error:
                        record['status'] = 'error'
                        record['preflight'].append(issue('PRODUCER_PROTOCOL', 'protocol', error))
            except (OSError, subprocess.SubprocessError) as error:
                record['status'] = 'error'
                record['preflight'].append(issue('CHECK_EXECUTION', 'execution', error))
            finally:
                shutil.rmtree(rootdir)
    after_hash, after_bytes = project.hash_bounded(translator, 256 * 1024 * 1024)
    if (after_hash, after_bytes) != (tool_hash, tool_bytes):
        raise project.Invalid('translator changed during diagnostic checking')
    envelope['complete'] = all(r['complete'] for r in envelope['root_checks'])
    envelope['truncated'] = any(r['truncated'] for r in envelope['root_checks'])
    envelope['status'] = 'checked' if all(r['status'] == 'checked' for r in envelope['root_checks']) else 'rejected'
    return envelope, limits


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('check',))
    parser.add_argument('manifest', type=Path)
    parser.add_argument('--translator', type=Path, required=True)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--diagnostic-limit', type=int, default=256, choices=range(1, 4097), metavar='1..4096')
    parser.add_argument('--unit-diagnostic-limit', type=int, default=64, choices=range(1, 4097), metavar='1..4096')
    args = parser.parse_args(argv)
    def cancel(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, cancel)
    try:
        manifest_path = args.manifest.resolve()
        if args.out:
            manifest, _, _ = project.load_manifest(manifest_path)
            protected = {manifest_path, args.translator.resolve()} | {manifest_path.parent / name for name in project.input_names(manifest)}
            demand(args.out.resolve() not in {p.resolve() for p in protected}, 'report destination overlaps an input or producer')
        report, limits = check_project(manifest_path, args.translator, args.diagnostic_limit,
                                       unit_limit=args.unit_diagnostic_limit)
        encoded = project.report_bytes(report, limits)
        if args.out:
            project.atomic_report(args.out, encoded, False)
        print(encoded.decode('utf-8'), end='')
        return 0 if report['status'] == 'checked' else 1
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(json.dumps({'schema': 1, 'kind': 'air2lean-project-diagnostics', 'diagnostics':
                         [issue('PROJECT_INPUT', 'import', error)]}), file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print(json.dumps({'schema': 1, 'kind': 'air2lean-project-diagnostics', 'diagnostics':
                         [issue('CANCELLED', 'execution', 'diagnostic check interrupted')]}), file=sys.stderr)
        return 130


if __name__ == '__main__':
    sys.exit(main())
