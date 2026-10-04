#!/usr/bin/env python3
"""Check selected project AIR with a versioned diagnostic producer; emit no Lean."""
import argparse
import copy
import json
import os
from pathlib import Path
import resource
import signal
import shutil
import subprocess
import sys
import tempfile
import time

import project

PROTOCOL_HEAD = '266dfacf7fcbec93aa3c2ce8f0932891a8c695c1'
KIND = 'air2lean-check-diagnostics'
CODES = frozenset('CLI_ARGUMENTS INPUT_READ INPUT_LIMIT JSON_SYNTAX AIR_DECODE EXPORTER_UNSUPPORTED OPTIMIZED_UNSUPPORTED CANONICAL_FAILURE NORMALIZATION_FAILURE STRUCTURE_FAILURE TYPE_FAILURE GLOBAL_FAILURE MEMORY_FAILURE INSTRUCTION_FAILURE CONSTANT_FAILURE SIGNATURE_FAILURE MODEL_FAILURE PROGRAM_FAILURE PROFILE_FAILURE DUPLICATE_FUNCTION CALLEE_MISSING CALLEE_BLOCKED CALLEE_AMBIGUOUS PREREQUISITE_SKIPPED'.split())
PHASES = frozenset('cli input decode canonicalize normalize check program profile'.split())
CATEGORIES = frozenset('malformed_input unsupported_semantics validation_failure resource_limit io_failure skipped_prerequisite'.split())
DEPENDENCIES = 'selected_normalized_direct_calls_and_spawn_workers'
REPORT_KEYS = ('schema', 'kind', 'status', 'complete', 'truncated', 'diagnostic_limit',
               'diagnostics_observed', 'diagnostic_payload_bytes', 'diagnostics', 'files',
               'scope', 'proof_status', 'runtime_outcomes', 'dependency_completeness', 'source_correspondence')
DIAGNOSTIC_KEYS = ('code', 'phase', 'category', 'message', 'message_truncated', 'file', 'function',
                   'anchor', 'source_span', 'source_span_status', 'dependency_chain',
                   'dependency_scope', 'prerequisites', 'first_error_in_unit')


def demand(ok, message):
    if not ok:
        raise project.Invalid(message)


def natural(value, maximum=None):
    return type(value) is int and value >= 0 and (maximum is None or value <= maximum)


def text(value, nullable=False):
    return (nullable and value is None) or (isinstance(value, str) and '\0' not in value)


def validate_receipt(raw, returncode, mapping, air_dir, limit):
    """Reject unknown schema/vocabulary and inconsistent evidence, without parsing messages."""
    demand(len(raw) <= project.LIMITS['max_output_bytes'], 'diagnostic receipt exceeds byte bound')
    receipt = project.bounded_json(raw, project.LIMITS)
    project.obj(receipt, REPORT_KEYS)
    demand(type(receipt['schema']) is int and receipt['schema'] == 1 and receipt['kind'] == KIND,
           'unsupported diagnostic protocol')
    demand(receipt['status'] in ('checked', 'rejected') and
           returncode == (0 if receipt['status'] == 'checked' else 1), 'diagnostic exit/status mismatch')
    for key in ('complete', 'truncated'):
        demand(type(receipt[key]) is bool, f'invalid {key}')
    demand(type(receipt['diagnostic_limit']) is int and receipt['diagnostic_limit'] == limit,
           'diagnostic limit mismatch')
    demand(natural(receipt['diagnostics_observed']) and natural(receipt['diagnostic_payload_bytes'], 1024 * 1024),
           'invalid diagnostic counters')
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
        demand(d['source_span'] is None and d['source_span_status'] == 'unavailable_in_AIR',
               'unexpected source span')
        demand(d['dependency_scope'] == DEPENDENCIES, 'unknown dependency scope')
        for key in ('dependency_chain', 'prerequisites'):
            demand(isinstance(d[key], list) and all(text(v) for v in d[key]), 'invalid diagnostic context')
        demand(len(d['dependency_chain']) <= 257, 'dependency chain exceeds producer bound')
    if receipt['truncated'] or any(d['first_error_in_unit'] for d in diagnostics):
        demand(not receipt['complete'], 'hidden diagnostic incompleteness')
    payload = sum(len(json.dumps(d, ensure_ascii=False, separators=(',', ':')).encode('utf-8')) for d in diagnostics)
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
    # Original bytes are hashed before this copy. Map only paths supplied to this invocation.
    mapped = copy.deepcopy(receipt)
    for d in mapped['diagnostics']:
        d['file'] = mapping.get(d['file'], '${SELECTED_AIR}' if d['file'] == str(air_dir) else None)
        d['message'] = d['message'].replace(str(air_dir), '${SELECTED_AIR}')
    for item in mapped['files']:
        item['file'] = mapping[item['file']]
    return mapped


def invoke(argv, cwd, limits):
    """Separate bounded byte streams, with the project's POSIX cancellation policy."""
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
        def constrain():
            resource.setrlimit(resource.RLIMIT_FSIZE, (limits['max_output_bytes'], limits['max_output_bytes']))
        child = subprocess.Popen(argv, cwd=cwd, stdout=stdout, stderr=stderr,
                                 start_new_session=True, preexec_fn=constrain)
        def kill_group():
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()
        def size():
            return os.fstat(stdout.fileno()).st_size + os.fstat(stderr.fileno()).st_size
        deadline = time.monotonic() + limits['timeout_seconds']
        failure = None
        try:
            while child.poll() is None:
                if time.monotonic() >= deadline:
                    failure = 'CHECK_TIMEOUT'
                    break
                if size() > limits['max_output_bytes']:
                    failure = 'CHECK_OUTPUT_LIMIT'
                    break
                time.sleep(.02)
            if failure:
                kill_group()
            else:
                try:
                    os.killpg(child.pid, 0)
                except ProcessLookupError:
                    pass
                else:
                    kill_group()
                    failure = 'CHECK_DESCENDANTS'
        except BaseException:
            kill_group()
            raise
        if size() > limits['max_output_bytes']:
            failure = failure or 'CHECK_OUTPUT_LIMIT'
        stdout.seek(0)
        stderr.seek(0)
        out = stdout.read(limits['max_output_bytes'])
        err = stderr.read(max(0, limits['max_output_bytes'] - len(out)))
        return {'returncode': child.returncode, 'stdout': out, 'stderr': err, 'failure': failure}


def issue(code, stage, message, path=None):
    return {'code': code, 'stage': stage, 'message': str(message), 'path': path,
            'source_span': None, 'source_span_status': 'unavailable_in_AIR'}


def preflight_air(data, profile, limits):
    """Classify at known validation boundaries, independent of legacy AIR_JSON text."""
    issues = {}
    for name, raw in data.items():
        local = issues[name] = []
        try:
            air = project.bounded_json(raw, limits)
        except (ValueError, UnicodeError, RecursionError) as error:
            local.append(issue('AIR_SYNTAX', 'import', error, name))
            continue
        if not isinstance(air, dict) or type(air.get('schema')) is not int or not 1 <= air['schema'] <= 12:
            local.append(issue('AIR_SCHEMA', 'schema', 'unsupported or malformed AIR schema', name))
            continue
        if profile is None:
            continue
        if air.get('zig_version') != profile['zig_version'] or air.get('target_endian', profile.get('endian', 'little')) != profile.get('endian', 'little'):
            local.append(issue('AIR_PROFILE', 'profile', 'AIR version/endian differs from manifest profile', name))
        if profile['name'] == 'legacy-abi64-le':
            if air['schema'] > 11 or 'profile' in air:
                local.append(issue('AIR_PROFILE', 'profile', 'profiled AIR cannot use a legacy manifest profile', name))
        else:
            try:
                project.validate_profile(air.get('profile'))
                demand(air['schema'] == 12 and air['profile'] == profile, 'AIR profile differs from manifest profile')
            except ValueError as error:
                local.append(issue('AIR_PROFILE', 'profile', error, name))
    return issues


def check_project(manifest_path, translator, limit, runner=invoke):
    manifest, limits, data, evidence = project.collect(manifest_path)
    translator = translator.resolve(strict=True)
    tool_hash, tool_bytes = project.hash_bounded(translator, 256 * 1024 * 1024)
    envelope = {'schema': 1, 'kind': 'air2lean-project-diagnostics', 'evidence': evidence,
                'translator': {'path': str(translator), 'sha256': tool_hash, 'bytes': tool_bytes},
                'producer_protocol': {'schema': 1, 'kind': KIND, 'reference_revision': PROTOCOL_HEAD,
                                      'qualification': 'not_attested_by_adapter'},
                'root_checks': [], 'complete': True, 'truncated': False,
                'proof_status': 'not_run', 'runtime_outcomes': 'not_observed', 'source_correspondence': 'not_attested'}
    air_data = {name: data[name] for root in manifest['roots'] for name in root['air'] if name in data}
    preflight = preflight_air(air_data, evidence['profile'], limits)
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
                    '--diagnostic-limit', str(limit)]
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
                        parsed = validate_receipt(result['stdout'], result['returncode'], mapping, air_dir, limit)
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
    parser.add_argument('command', choices=('diagnosticcheck',))
    parser.add_argument('manifest', type=Path)
    parser.add_argument('--translator', type=Path, required=True)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--diagnostic-limit', type=int, default=256, choices=range(1, 4097), metavar='1..4096')
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
        report, limits = check_project(manifest_path, args.translator, args.diagnostic_limit)
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
