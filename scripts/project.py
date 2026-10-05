#!/usr/bin/env python3
"""Bounded project preflight, translation, and hash-bound evidence (stdlib only)."""
import argparse
from contextlib import ExitStack
import hashlib
import json
import math
import os
from pathlib import Path
import re
import resource
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from typing import NamedTuple, Optional

SCHEMA = 1
STAGES = ('analyzed', 'exported', 'translated', 'compiled', 'tested', 'proved')
OUTCOMES = ('exact_match', 'host_difference', 'undefined_behavior', 'unspecified_behavior',
            'nondeterministic_valid', 'unsupported_semantics', 'panic', 'error_return',
            'illegal_behavior', 'deadlock', 'divergence', 'search_cap', 'skipped', 'proof_exclusion')
LIMITS = {'max_file_bytes': 8 * 1024 * 1024, 'max_total_bytes': 64 * 1024 * 1024,
          'max_json_depth': 128, 'max_files': 4096, 'max_roots': 256, 'max_total_output_bytes': 64 * 1024 * 1024, 'timeout_seconds': 60, 'max_output_bytes': 8 * 1024 * 1024}
IDENT = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')


class Invalid(ValueError):
    pass


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False) + '\n').encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def obj(value, required, optional=()):
    if not isinstance(value, dict) or set(value) - set(required) - set(optional) or set(required) - set(value):
        raise Invalid(f'expected object with required keys {list(required)} and optional keys {list(optional)}')


def string(value):
    if not isinstance(value, str) or not value or '\0' in value:
        raise Invalid('expected nonempty string without NUL')
    return value


def strings(value, nonempty=False):
    if not isinstance(value, list) or (nonempty and not value):
        raise Invalid('expected string list' + (' with at least one entry' if nonempty else ''))
    for item in value:
        string(item)
    if len(set(value)) != len(value):
        raise Invalid('duplicate list entry')


def reject_constant(value):
    raise Invalid(f'invalid JSON number: {value}')


def bounded_json(data, limits):
    if len(data) > limits['max_file_bytes']:
        raise Invalid('input exceeds max_file_bytes')
    # Reject depth before json.loads can recurse. Braces inside strings are ignored.
    depth = 0
    quoted = escaped = False
    for ch in data.decode('utf-8'):
        if quoted:
            if escaped:
                escaped = False
            elif ch == '\\':
                escaped = True
            elif ch == '"':
                quoted = False
        elif ch == '"':
            quoted = True
        elif ch in '[{':
            depth += 1
            if depth > limits['max_json_depth']:
                raise Invalid('input exceeds max_json_depth')
        elif ch in ']}':
            depth -= 1
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise Invalid(f'duplicate JSON key: {key}')
            result[key] = value
        return result
    def finite_float(value):
        parsed = float(value)
        if not math.isfinite(parsed):
            raise Invalid(f'invalid nonfinite JSON number: {value}')
        return parsed
    return json.loads(data, object_pairs_hook=pairs, parse_float=finite_float,
                      parse_constant=reject_constant)


def path_under(base, name):
    string(name)
    relative = Path(name)
    if relative.is_absolute() or '..' in relative.parts:
        raise Invalid(f'path must be relative without parent traversal: {name}')
    path = base / relative
    if not path.resolve().is_relative_to(base.resolve()):
        raise Invalid(f'path escapes project directory: {name}')
    if not path.is_file():
        raise Invalid(f'input file missing: {name}')
    return path


def _file_chunks(path, cap, charge):
    # Unbuffered reads expose each returned chunk before a later read can fail.
    # O_NONBLOCK prevents FIFO/device opens from bypassing subprocess timeouts.
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NONBLOCK), 'rb', 0) as handle:
        if not stat.S_ISREG(os.fstat(handle.fileno()).st_mode):
            raise Invalid(f'input is not a regular file: {path.name}')
        total = 0
        while True:
            chunk = handle.read(min(1024 * 1024, cap + 1 - total))
            if not chunk:
                return
            if charge is not None:
                charge(len(chunk))
            total += len(chunk)
            if total > cap:
                raise Invalid(f'input exceeds byte limit: {path.name}')
            yield chunk


def read_bounded(path, cap, *, charge=None):
    return b''.join(_file_chunks(path, cap, charge))


def hash_bounded(path, cap, *, charge=None):
    """Hash a regular file in chunks, detecting cap+1 bytes even if it grows."""
    hashed = hashlib.sha256()
    total = 0
    for chunk in _file_chunks(path, cap, charge):
        hashed.update(chunk)
        total += len(chunk)
    return hashed.hexdigest(), total


def load_manifest(path):
    raw = read_bounded(path, LIMITS['max_file_bytes'])
    manifest = bounded_json(raw, LIMITS)
    obj(manifest, ('schema', 'profile', 'float_semantics', 'source_closure', 'components', 'roots', 'allowed_assumptions'), ('limits',))
    if type(manifest['schema']) is not int or manifest['schema'] != SCHEMA:
        raise Invalid('unsupported manifest schema')
    limits = dict(LIMITS)
    supplied = manifest.get('limits', {})
    obj(supplied, (), LIMITS)
    for key, value in supplied.items():
        if type(value) is not int or not 1 <= value <= LIMITS[key]:
            raise Invalid(f'{key} must be an integer from 1 through {LIMITS[key]}')
        limits[key] = value
    if manifest['float_semantics'] not in ('ieee', 'compiler-rt'):
        raise Invalid('float_semantics must be ieee or compiler-rt')
    strings(manifest['source_closure'], True)
    strings(manifest['allowed_assumptions'])
    obj(manifest['components'], ('compiler_patch', 'runtime', 'toolchain'))
    for values in manifest['components'].values():
        strings(values, True)
    # Profile is a versioned externally validated artifact, never a target qualification claim.
    string(manifest['profile'])
    path_under(path.parent, manifest['profile'])
    if not isinstance(manifest['roots'], list) or not manifest['roots']:
        raise Invalid('roots must be a nonempty list')
    if len(manifest['roots']) > limits['max_roots']:
        raise Invalid('input exceeds max_roots')
    ids = set()
    for root in manifest['roots']:
        obj(root, ('id', 'function', 'air', 'namespace', 'prefix', 'contracts', 'goals', 'assumptions', 'exclusions'))
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*', string(root['id'])) or root['id'] in ids:
            raise Invalid('invalid or duplicate root id')
        ids.add(root['id'])
        string(root['function'])
        if not IDENT.fullmatch(string(root['namespace'])):
            raise Invalid('namespace must contain dot-separated Lean identifiers')
        if not isinstance(root['prefix'], str) or '\0' in root['prefix']:
            raise Invalid('prefix must be a string without NUL')
        for key in ('air', 'contracts', 'assumptions', 'exclusions'):
            strings(root[key], key == 'air')
        if set(root['assumptions']) - set(manifest['allowed_assumptions']):
            raise Invalid(f'root {root["id"]} uses assumptions outside allowlist')
        if not isinstance(root['goals'], list):
            raise Invalid('goals must be a list')
        for goal in root['goals']:
            obj(goal, ('theorem', 'strength', 'domain'))
            string(goal['theorem'])
            string(goal['domain'])
            if goal['strength'] not in ('safety', 'partial_correctness', 'total_correctness', 'resource_bound', 'correspondence'):
                raise Invalid('invalid theorem strength')
    return manifest, raw, limits


def validate_profile(profile):
    if isinstance(profile, dict) and profile.get('name') == 'legacy-abi64-le':
        obj(profile, ('name', 'zig_version'))
        string(profile['zig_version'])
        return
    required = ('name', 'target_triple', 'pointer_bits', 'endian', 'abi', 'zig_version',
                'backend', 'cpu', 'features', 'build_mode', 'float_mode', 'error_set_bits',
                'error_layout', 'export_stage', 'error_tracing')
    obj(profile, required)
    for key in ('target_triple', 'abi', 'zig_version', 'backend', 'cpu'):
        string(profile[key])
    strings(profile['features'])
    if type(profile['error_tracing']) is not bool:
        raise Invalid('error_tracing must be boolean')
    triple = profile['target_triple'].split('-')
    if (len(triple) != 3 or (triple[0], triple[1].split('.')[0]) not in (('x86_64', 'linux'), ('aarch64', 'macos'))
            or triple[2].split('.')[0] != profile['abi']):
        raise Invalid('profile requires a supported architecture/OS and matching ABI')
    if (profile['name'] != 'abi64-le-v1' or type(profile['pointer_bits']) is not int or profile['pointer_bits'] != 64
            or profile['endian'] != 'little' or type(profile['error_set_bits']) is not int or profile['error_set_bits'] != 16
            or profile['float_mode'] != 'per-instruction' or profile['error_layout'] != 'type-table'
            or profile['export_stage'] != 'analyzed-air'
            or profile['build_mode'] not in ('Debug', 'ReleaseSafe', 'ReleaseFast', 'ReleaseSmall')):
        raise Invalid('unsupported or malformed profile')


def git_state(base):
    def git(*args):
        return subprocess.run(['git', '-C', str(base), *args], stdout=subprocess.PIPE,
                              stderr=subprocess.DEVNULL, timeout=5, check=True).stdout
    try:
        return {'revision': git('rev-parse', 'HEAD').decode().strip(),
                'dirty': bool(git('status', '--porcelain', '--untracked-files=all'))}
    except (OSError, subprocess.SubprocessError):
        return {'revision': None, 'dirty': None, 'reason': 'Git provenance unavailable'}


def diagnostic(code, message, root=None, path=None, category='malformed_input'):
    return {'code': code, 'category': category, 'message': str(message), 'root': root,
            'path': path, 'source_span': None, 'dependency_chain': [],
            'location_note': 'AIR lacks reliable source/dependency locations; none inferred'}


def input_names(manifest):
    names = set(manifest['source_closure']) | {manifest['profile']}
    for values in manifest['components'].values():
        names.update(values)
    for root in manifest['roots']:
        names.update(root['air'])
        names.update(root['contracts'])
    return names


class AIRBoundary(NamedTuple):
    """Compact import/schema/profile observations; never retains decoded AIR trees."""
    syntax_error: Optional[str]
    schema_valid: bool
    version_endian_mismatch: bool
    profile_error: Optional[str]


def air_boundary(air, profile, syntax_error=None):
    schema_valid = (isinstance(air, dict) and type(air.get('schema')) is int
                    and 1 <= air['schema'] <= 12)
    mismatch = False
    profile_error = None
    if schema_valid and profile is not None:
        mismatch = (air.get('zig_version') != profile['zig_version'] or
            air.get('target_endian', profile.get('endian', 'little')) != profile.get('endian', 'little'))
        if profile['name'] == 'legacy-abi64-le':
            if air['schema'] > 11 or 'profile' in air:
                profile_error = 'profiled AIR cannot use a legacy manifest profile'
        else:
            try:
                validate_profile(air.get('profile'))
                if air['schema'] != 12 or air['profile'] != profile:
                    raise Invalid('AIR profile differs from manifest profile')
            except ValueError as error:
                profile_error = str(error)
    return AIRBoundary(syntax_error, schema_valid, mismatch, profile_error)


def summarize_air(content, profile, limits, *, include_boundary=False):
    """Root-independent observations, replayed with each root's ID and path."""
    observed = None
    unsupported = 0
    diagnostics = []
    air = None
    syntax_error = None
    try:
        try:
            air = bounded_json(content, limits)
        except (ValueError, UnicodeError) as error:
            syntax_error = str(error)
            raise
        if not isinstance(air, dict) or not isinstance(air.get('name'), str):
            raise Invalid('AIR must be an object with a function name')
        observed = air['name']
        if type(air.get('schema')) is not int or not 1 <= air['schema'] <= 12:
            raise Invalid('unsupported or malformed AIR schema')
        pending = [air.get('body', [])]
        while pending:
            node = pending.pop()
            if isinstance(node, list):
                pending.extend(node)
            elif isinstance(node, dict):
                if node.get('unsupported') is True:
                    unsupported += 1
                    diagnostics.append(('AIR_EXPORT_UNSUPPORTED',
                        f"exporter marked instruction {node.get('id')} tag {node.get('tag')} unsupported",
                        'unsupported_semantics'))
                pending.extend(node.values())
        # Preserve observations before metadata errors, including unsupported marker order.
        if profile and 'zig_version' in profile and air.get('zig_version') != profile['zig_version']:
            raise Invalid('AIR zig_version differs from declared profile')
        if profile and air.get('target_endian', profile.get('endian', 'little')) != profile.get('endian', 'little'):
            raise Invalid('AIR target_endian differs from declared profile')
        if profile and profile['name'] == 'abi64-le-v1':
            validate_profile(air.get('profile'))
            if air['schema'] != 12 or air['profile'] != profile:
                raise Invalid('AIR profile missing or differs from declared profile')
        if profile and profile['name'] == 'legacy-abi64-le' and (air['schema'] > 11 or 'profile' in air):
            raise Invalid('profiled AIR cannot be relabeled as legacy')
    except (ValueError, UnicodeError) as error:
        diagnostics.append(('AIR_JSON', str(error), 'malformed_input'))
    summary = (observed, unsupported, diagnostics)
    if include_boundary:
        return (*summary, air_boundary(air, profile, syntax_error))
    return summary


def collect(path, *, air_boundaries=None):
    """Return the existing four-tuple; optionally fill compact per-file boundaries."""
    manifest, raw, limits = load_manifest(path)
    files = {'manifest': {'sha256': digest(raw), 'bytes': len(raw)}}
    data = {}
    retained = {manifest['profile']} | {name for root in manifest['roots'] for name in root['air']}
    diagnostics = []
    total = len(raw)
    names = input_names(manifest)
    if len(names) > limits['max_files']:
        raise Invalid('input exceeds max_files')
    if total > limits['max_total_bytes']:
        raise Invalid('manifest exceeds max_total_bytes')
    def charge(size):
        nonlocal total
        total += size
    for name in sorted(names):
        try:
            if total > limits['max_total_bytes']:
                raise Invalid('input exceeds max_total_bytes')
            cap = min(limits['max_file_bytes'], limits['max_total_bytes'] - total)
            source = path_under(path.parent, name)
            if name in retained:
                content = read_bounded(source, cap, charge=charge)
                data[name] = content
                sha256, size = digest(content), len(content)
            else:
                sha256, size = hash_bounded(source, cap, charge=charge)
            files['input/' + name] = {'sha256': sha256, 'bytes': size}
        except (OSError, Invalid) as error:
            diagnostics.append(diagnostic('INPUT_FILE', error, path=name))
    profile = None
    if manifest['profile'] in data:
        try:
            profile = bounded_json(data[manifest['profile']], limits)
            validate_profile(profile)
        except (ValueError, UnicodeError) as error:
            diagnostics.append(diagnostic('PROFILE_JSON', error, path=manifest['profile']))
            profile = None
    shared_names = set(manifest['source_closure']) | {manifest['profile']}
    for component in manifest['components'].values():
        shared_names.update(component)
    shared_failed = any(d['path'] in shared_names for d in diagnostics)
    roots = []
    air_summaries = {}
    for root in manifest['roots']:
        statuses = {stage: {'status': 'not_run', 'reason': 'stage not executed by this command'} for stage in STAGES}
        statuses['exported']['reason'] = 'supplied AIR is input evidence; no compiler export was executed'
        statuses['proved']['reason'] = 'declared theorem goals are not checked proof evidence'
        record = dict(root, stages=statuses, observed_functions=[], outcomes={key: 0 for key in OUTCOMES})
        blockers_before = len(diagnostics)
        root_input_failed = any(d['path'] in set(root['air'] + root['contracts']) for d in diagnostics)
        for name in root['air']:
            if name not in data:
                diagnostics.append(diagnostic('AIR_MISSING', 'AIR unavailable', root['id'], name))
                continue
            if name not in air_summaries:
                summary = summarize_air(data[name], profile, limits,
                                        include_boundary=air_boundaries is not None)
                air_summaries[name] = summary[:3]
                if air_boundaries is not None:
                    air_boundaries[name] = summary[3]
            observed, unsupported, issues = air_summaries[name]
            if observed is not None:
                record['observed_functions'].append(observed)
            record['outcomes']['unsupported_semantics'] += unsupported
            diagnostics.extend(diagnostic(code, message, root['id'], name, category)
                               for code, message, category in issues)
        if root['function'] not in record['observed_functions']:
            diagnostics.append(diagnostic('ROOT_NOT_PRESENT', 'root function absent from supplied AIR', root['id']))
        record['input_validation'] = {'status': 'failed' if shared_failed or root_input_failed or len(diagnostics) > blockers_before else 'passed',
                                      'scope': 'declared input readability, bounded JSON syntax, root presence and profile metadata only'}
        record['stages']['analyzed'] = {'status': 'not_run', 'reason': 'JSON syntax preflight is not Zig semantic analysis'}
        record['outcomes']['proof_exclusion'] = len(root['exclusions'])
        roots.append(record)
    report = {'schema': SCHEMA, 'kind': 'air2lean-project-evidence', 'manifest_sha256': digest(raw),
              'float_semantics': manifest['float_semantics'], 'profile': profile, 'files': files, 'git': git_state(path.parent), 'roots': roots,
              'diagnostics': diagnostics, 'trust_scope': [
                  'Declared source closure is hashed; completeness is not established by compiler dependencies.',
                  'Input AIR does not attest source export or shipping backend correspondence.',
                  'Translator, exporter, compiler, runtime models and target assumptions remain trusted.',
                  'Theorem declarations, command success and sampled tests do not establish theorem dependency closure.'],
              'outcome_note': 'Zero denotes no recorded observations, not proved absence of an outcome.',
              'capabilities': {'json_preflight': True, 'translation': True, 'compiler_export': False,
                               'proof_checking': False, 'differential_testing': False, 'incremental_cache': False}}
    return manifest, limits, data, report


def _run_bounded(argv, cwd, limits, *, merged):
    """Raw bounded POSIX execution shared by adapters with different receipt policies."""
    with ExitStack() as streams:
        stdout = streams.enter_context(tempfile.TemporaryFile())
        stderr = stdout if merged else streams.enter_context(tempfile.TemporaryFile())
        logs = (stdout,) if merged else (stdout, stderr)
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
            return sum(os.fstat(log.fileno()).st_size for log in logs)
        deadline = time.monotonic() + limits['timeout_seconds']
        failure = None
        try:
            while child.poll() is None:
                if time.monotonic() >= deadline:
                    failure = 'timeout'
                    break
                if size() > limits['max_output_bytes']:
                    failure = 'output_limit'
                    break
                time.sleep(.02)
            if failure:
                kill_group()
            else:
                # A wrapper exiting before its helpers finish has not completed the stage.
                try:
                    os.killpg(child.pid, 0)
                except ProcessLookupError:
                    pass
                else:
                    kill_group()
                    failure = 'descendants'
        except BaseException:
            kill_group()
            raise
        if merged and failure:
            return {'returncode': child.returncode, 'stdout': b'', 'stderr': b'', 'failure': failure}
        if not merged and size() > limits['max_output_bytes']:
            failure = failure or 'output_limit'
        stdout.seek(0)
        out = stdout.read(limits['max_output_bytes'])
        err = b''
        if not merged:
            stderr.seek(0)
            err = stderr.read(max(0, limits['max_output_bytes'] - len(out)))
        if merged and size() > limits['max_output_bytes']:
            failure = failure or 'output_limit'
        return {'returncode': child.returncode, 'stdout': out, 'stderr': err, 'failure': failure}


def run_translation(argv, cwd, limits):
    result = _run_bounded(argv, cwd, limits, merged=True)
    failures = {'timeout': ('TRANSLATION_TIMEOUT', 'translator exceeded timeout'),
                'output_limit': ('TRANSLATION_OUTPUT_LIMIT', 'translator log exceeded limit'),
                'descendants': ('TRANSLATION_DESCENDANTS', 'translator exited with unfinished child processes')}
    if result['failure']:
        code, message = failures[result['failure']]
        return {'status': 'failed', 'code': code, 'message': message}
    passed = result['returncode'] == 0
    return {'status': 'passed' if passed else 'failed',
            'code': 'TRANSLATION_OK' if passed else 'TRANSLATION_FAILED',
            'returncode': result['returncode'],
            'message': result['stdout'].decode('utf-8', errors='replace'), 'argv': argv}


def translate(manifest, limits, data, report, translator, staging):
    if report['diagnostics']:
        return
    translator = translator.resolve(strict=True)
    report['translator'] = {'path': str(translator), 'sha256': hash_bounded(translator, 256 * 1024 * 1024)[0]}
    generated_bytes = 0
    log_bytes = 0
    for root, record in zip(manifest['roots'], report['roots']):
        if generated_bytes >= limits['max_total_output_bytes'] or log_bytes >= limits['max_total_output_bytes']:
            record['stages']['translated'] = {'status': 'not_run', 'reason': 'project output budget exhausted'}
            report['diagnostics'].append(diagnostic('PROJECT_OUTPUT_LIMIT', 'project output budget exhausted', root['id'], category='resource_limit'))
            continue
        rootdir = staging / root['id']
        rootdir.mkdir()
        air_dir = rootdir / 'air'
        air_dir.mkdir()
        for index, name in enumerate(root['air']):
            (air_dir / f'{index:06d}.json').write_bytes(data[name])
        output = rootdir / 'Gen.lean'
        argv = [str(translator), str(air_dir), '-o', str(output), '--namespace', root['namespace'], '--prefix', root['prefix'], '--float-semantics', manifest['float_semantics']]
        child_limits = dict(limits, max_output_bytes=min(limits['max_output_bytes'],
                            limits['max_total_output_bytes'] - generated_bytes,
                            limits['max_total_output_bytes'] - log_bytes))
        result = run_translation(argv, rootdir, child_limits)
        log_bytes += len(result.get('message', '').encode('utf-8'))
        if 'argv' in result:
            result['argv'] = [a.replace(str(staging), '${ARTIFACT_STAGING}') for a in result['argv']]
        if result['status'] == 'passed':
            try:
                generated = read_bounded(path_under(rootdir, 'Gen.lean'), child_limits['max_output_bytes'])
                generated_bytes += len(generated)
                if not generated:
                    raise Invalid('translator produced empty output')
                report['files'][f'generated/{root["id"]}/Gen.lean'] = {'sha256': digest(generated), 'bytes': len(generated)}
            except (OSError, Invalid) as error:
                result = {'status': 'failed', 'code': 'TRANSLATION_ARTIFACT', 'message': str(error)}
        shutil.rmtree(air_dir)
        record['stages']['translated'] = result
        if result['status'] == 'failed':
            shutil.rmtree(rootdir)  # Failed partial files must not accumulate outside the aggregate budget.
            report['diagnostics'].append(diagnostic(result['code'], result['message'], root['id'], category='translator_failure'))


def report_bytes(report, limits):
    encoder = json.JSONEncoder(sort_keys=True, indent=2, ensure_ascii=False)
    maximum = limits['max_total_output_bytes']
    encoded = bytearray()
    for chunk in encoder.iterencode(report):
        if len(chunk) > maximum - len(encoded):
            raise Invalid('report exceeds max_total_output_bytes')
        # A single string can be a large encoder chunk; bound each UTF-8 copy too.
        for offset in range(0, len(chunk), 65536):
            part = chunk[offset:offset + 65536].encode('utf-8')
            if len(part) > maximum - len(encoded):
                raise Invalid('report exceeds max_total_output_bytes')
            encoded.extend(part)
    if len(encoded) >= maximum:
        raise Invalid('report exceeds max_total_output_bytes')
    encoded.append(10)
    return bytes(encoded)


def atomic_report(path, encoded, overwrite):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as handle:
        temp = Path(handle.name)
        try:
            handle.write(encoded)
            handle.flush()
            os.fsync(handle.fileno())
        except BaseException:
            temp.unlink(missing_ok=True)
            raise
    try:
        if overwrite:
            os.replace(temp, path)
        else:
            os.link(temp, path)  # Atomic no-clobber publication, including concurrent writers.
    finally:
        temp.unlink(missing_ok=True)


def verify(path, artifact):
    manifest, limits, data, current = collect(path)
    stored = bounded_json(read_bounded(path_under(artifact, 'report.json'), LIMITS['max_total_bytes']),
                          dict(LIMITS, max_file_bytes=LIMITS['max_total_bytes']))
    obj(stored, ('schema', 'kind', 'files', 'manifest_sha256', 'translator'),
        ('float_semantics', 'profile', 'git', 'roots', 'diagnostics', 'trust_scope', 'outcome_note', 'capabilities'))
    if current['diagnostics'] or current['manifest_sha256'] != stored.get('manifest_sha256'):
        raise Invalid('manifest or inputs invalid/stale')
    if type(stored.get('schema')) is not int or stored.get('schema') != SCHEMA or stored.get('kind') != 'air2lean-project-evidence' or not isinstance(stored.get('files'), dict):
        raise Invalid('invalid artifact report')
    expected_names = set(current['files']) | {f'generated/{root["id"]}/Gen.lean' for root in manifest['roots']}
    if set(stored['files']) != expected_names:
        raise Invalid('artifact inventory differs from complete project output')
    for name, expected in stored['files'].items():
        obj(expected, ('sha256', 'bytes'))
        if type(expected['bytes']) is not int or not 0 <= expected['bytes'] <= LIMITS['max_total_bytes']:
            raise Invalid('invalid artifact byte count')
        if not isinstance(expected['sha256'], str) or not re.fullmatch('[0-9a-f]{64}', expected['sha256']):
            raise Invalid('invalid artifact digest')
        if name.startswith('generated/'):
            if not re.fullmatch(r'generated/[A-Za-z][A-Za-z0-9_-]*/Gen\.lean', name):
                raise Invalid('invalid generated artifact path')
            source = path_under(artifact, name.removeprefix('generated/'))
            content = read_bounded(source, LIMITS['max_output_bytes'])
            actual = digest(content)
            actual_bytes = len(content)
        else:
            if name not in current['files']:
                raise Invalid('unknown artifact input path')
            actual = current['files'][name]['sha256']
            actual_bytes = current['files'][name]['bytes']
        if actual != expected['sha256'] or actual_bytes != expected['bytes']:
            raise Invalid(f'artifact hash mismatch: {name}')
    tool = stored['translator']
    obj(tool, ('path', 'sha256'))
    if hash_bounded(Path(string(tool['path'])), 256 * 1024 * 1024)[0] != tool['sha256']:
        raise Invalid('translator executable hash mismatch')
    return {'status': 'hashes_match', 'proof_status': 'not_attested', 'artifact': str(artifact)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('report', 'translate', 'verify'))
    parser.add_argument('manifest', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--translator', type=Path)
    parser.add_argument('--artifact', type=Path)
    parser.add_argument('--overwrite', action='store_true', help='replace a report file; translation artifacts are immutable')
    args = parser.parse_args(argv)
    def cancel(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, cancel)
    try:
        if args.command == 'verify':
            if not args.artifact:
                raise Invalid('verify requires --artifact')
            print(json.dumps(verify(args.manifest.resolve(), args.artifact.resolve())))
            return 0
        manifest, limits, data, report = collect(args.manifest.resolve())
        if args.command == 'translate':
            if not args.out or not args.translator or args.overwrite:
                raise Invalid('translate requires --out, --translator and no --overwrite; use a fresh artifact directory')
            args.out = args.out.resolve()
            args.out.parent.mkdir(parents=True, exist_ok=True)
            if args.out.exists():
                raise Invalid('artifact already exists; choose a fresh directory')
            with tempfile.TemporaryDirectory(prefix='.air2lean-', dir=args.out.parent) as temp:
                staging = Path(temp) / 'artifact'
                staging.mkdir()
                translate(manifest, limits, data, report, args.translator, staging)
                encoded = report_bytes(report, limits)
                if not report['diagnostics']:
                    (staging / 'report.json').write_bytes(encoded)
                    if args.out.exists():
                        raise Invalid('artifact appeared during translation; refusing replacement')
                    os.rename(staging, args.out)
        else:
            if args.out:
                protected = {args.manifest.resolve()} | {args.manifest.resolve().parent / name for name in input_names(manifest)}
                if args.out.resolve() in {p.resolve() for p in protected}:
                    raise Invalid('report destination overlaps an input file')
            encoded = report_bytes(report, limits)
            if args.out:
                atomic_report(args.out, encoded, args.overwrite)
        print(encoded.decode('utf-8'), end='')
        return 1 if report['diagnostics'] else 0
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(json.dumps({'schema': SCHEMA, 'diagnostics': [diagnostic('PROJECT_INPUT', error)]}), file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print(json.dumps({'schema': SCHEMA, 'diagnostics': [diagnostic('CANCELLED', 'project command interrupted', category='cancelled')]}), file=sys.stderr)
        return 130


if __name__ == '__main__':
    sys.exit(main())
