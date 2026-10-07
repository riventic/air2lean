#!/usr/bin/env python3
"""Bounded project preflight, translation, and hash-bound evidence (stdlib only)."""
import argparse
from contextlib import ExitStack
import datetime
import hashlib
import json
import math
import os
from pathlib import Path
import platform
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
    obj(manifest, ('schema', 'profile', 'float_semantics', 'source_closure', 'components', 'roots', 'allowed_assumptions'), ('limits', 'spawn_policy', 'check'))
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
    spawn_policy(manifest)
    check_budget(manifest)
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
        obj(root, ('id', 'function', 'air', 'namespace', 'prefix', 'contracts', 'goals', 'assumptions', 'exclusions'), ('generated',))
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
        if 'generated' in root:
            string(root['generated'])
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


def spawn_policy(manifest):
    policy = manifest.get('spawn_policy', 'available')
    if not isinstance(policy, str) or policy not in ('available', 'fallible'):
        raise Invalid('spawn_policy must be available or fallible')
    return policy


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
        if 'generated' in root:
            names.add(root['generated'])
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
              'float_semantics': manifest['float_semantics'], 'spawn_policy': spawn_policy(manifest), 'profile': profile, 'files': files, 'git': git_state(path.parent), 'roots': roots,
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
        argv = [str(translator), str(air_dir), '-o', str(output), '--namespace', root['namespace'], '--prefix', root['prefix'], '--float-semantics', manifest['float_semantics'], '--spawn-policy', spawn_policy(manifest)]
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


def publish_translation(manifest, limits, data, report, translator, out):
    """Translate into private staging; rename to the fresh `out` only when every root passed."""
    out.parent.mkdir(parents=True, exist_ok=True)
    if out.exists():
        raise Invalid('artifact already exists; choose a fresh directory')
    with tempfile.TemporaryDirectory(prefix='.air2lean-', dir=out.parent) as temp:
        staging = Path(temp) / 'artifact'
        staging.mkdir()
        translate(manifest, limits, data, report, translator, staging)
        encoded = report_bytes(report, limits)
        if not report['diagnostics']:
            (staging / 'report.json').write_bytes(encoded)
            if out.exists():
                raise Invalid('artifact appeared during translation; refusing replacement')
            os.rename(staging, out)
    return encoded

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


def verify_spawn_policy(manifest, stored):
    effective = spawn_policy(manifest)
    historical = 'spawn_policy' not in stored
    if spawn_policy(stored) != effective:
        raise Invalid('artifact spawn_policy differs from manifest')
    # A pre-policy receipt can only describe the historical available default.
    # New receipts also bind each actual translation invocation to that selection.
    roots = stored.get('roots', [])
    if not isinstance(roots, list):
        raise Invalid('invalid artifact roots')
    if not historical and ([r.get('id') if isinstance(r, dict) else None for r in roots]
                           != [r['id'] for r in manifest['roots']]):
        raise Invalid('artifact policy evidence requires complete root inventory')
    for root in roots:
        if not isinstance(root, dict):
            raise Invalid('invalid artifact root')
        stages = root.get('stages', {})
        if not isinstance(stages, dict):
            raise Invalid('invalid artifact stages')
        translated = stages.get('translated', {})
        if not isinstance(translated, dict):
            raise Invalid('invalid artifact translation evidence')
        argv = translated.get('argv', [])
        if not isinstance(argv, list) or any(not isinstance(a, str) for a in argv):
            raise Invalid('invalid artifact translation argv')
        # The wrapper emits two positional arguments followed by option/value pairs.
        # Values (notably --prefix) may themselves look like option names.
        positions = []
        i = 2
        while i < len(argv):
            if argv[i] not in ('-o', '--namespace', '--prefix', '--float-semantics', '--spawn-policy') or i + 1 >= len(argv):
                raise Invalid('invalid artifact translation argv')
            if argv[i] == '--spawn-policy':
                positions.append(i)
            i += 2
        if not positions and historical:
            continue
        if (translated.get('status') != 'passed' or len(positions) != 1
                or positions[0] + 1 >= len(argv) or argv[positions[0] + 1] != effective):
            raise Invalid('artifact translation argv does not match spawn_policy')


def verify(path, artifact):
    manifest, limits, data, current = collect(path)
    stored = bounded_json(read_bounded(path_under(artifact, 'report.json'), LIMITS['max_total_bytes']),
                          dict(LIMITS, max_file_bytes=LIMITS['max_total_bytes']))
    obj(stored, ('schema', 'kind', 'files', 'manifest_sha256', 'translator'),
        ('float_semantics', 'spawn_policy', 'profile', 'git', 'roots', 'diagnostics', 'trust_scope', 'outcome_note', 'capabilities'))
    if current['diagnostics'] or current['manifest_sha256'] != stored.get('manifest_sha256'):
        raise Invalid('manifest or inputs invalid/stale')
    if type(stored.get('schema')) is not int or stored.get('schema') != SCHEMA or stored.get('kind') != 'air2lean-project-evidence' or not isinstance(stored.get('files'), dict):
        raise Invalid('invalid artifact report')
    verify_spawn_policy(manifest, stored)
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


# ---------------------------------------------------------------------------
# Per-root verification coverage (I06). Joins manifest roots with a translation
# artifact, a proof receipt attempt (receipt/plan/audit/after JSON) and typed
# differential summaries. Every rule below can only lower a level; no evidence
# source can raise a root to functional verification on its own.

FUNCTIONAL = ('partial_correctness', 'total_correctness')
LEVELS = ('none', 'translated', 'compiled', 'tested_sampled', 'proved_scoped',
          'functionally_verified_partial', 'functionally_verified_total')
EVIDENCE_JSON = dict(LIMITS, max_file_bytes=64 * 1024 * 1024)
DIFF_FAILURES = ('mismatch', 'host_difference', 'input_failure', 'native_harness_failure')
DIFF_EXCLUSIONS = ('illegal_exclusion', 'unspecified_exclusion', 'search_cap', 'bounded_no_result')
DIFF_MATCHES = ('value_match', 'error_return_match', 'panic_match')


def stage(status, reason, **extra):
    return dict(extra, status=status, reason=reason)


def load_evidence(path):
    return bounded_json(read_bounded(path, EVIDENCE_JSON['max_file_bytes']), EVIDENCE_JSON)


def source_sha(row):
    return (row.get('target') or {}).get('sha256') if row.get('kind') == 'symlink' else row.get('sha256')


def run_receipt_verifier(verifier, attempt, limits):
    """The receipt tool owns staleness; any failure or non-current answer is stale."""
    result = _run_bounded([sys.executable, str(verifier), 'verify', str(attempt)], verifier.parent,
                          limits, merged=False)
    detail = (result['stderr'] or result['stdout']).decode('utf-8', errors='replace').strip()
    if result['failure'] or result['returncode'] != 0:
        return False, detail or result['failure'] or f'verifier exited {result["returncode"]}'
    try:
        answer = json.loads(result['stdout'])
    except ValueError:
        return False, 'verifier output is not JSON'
    if not isinstance(answer, dict) or answer.get('status') != 'current':
        return False, 'verifier did not report a current receipt'
    return True, 'proof receipt verifier reported current identities'


def load_receipt(attempt, verifier, limits):
    """Return (bundle, None) or (None, reason). The format is consumed, never extended."""
    try:
        attempt = attempt.resolve(strict=True)
        receipt, plan, audit, after = (load_evidence(path_under(attempt, name)) for name in
                                       ('receipt.json', 'plan.json', 'audit.json', 'after.json'))
        if (not isinstance(receipt, dict) or receipt.get('schema') != 1 or receipt.get('status') != 'audited'
                or not all(isinstance(x, dict) for x in (plan, audit, after))):
            return None, 'receipt is not a sealed audited schema-1 receipt'
        if audit.get('status') != 'pass' or not isinstance(audit.get('theorems'), list) or not isinstance(audit.get('nodes'), list):
            return None, 'receipt audit did not pass or lacks theorem/declaration inventory'
        if not isinstance(plan.get('modules'), list) or not isinstance(plan.get('root'), str):
            return None, 'receipt plan lacks module scope or repository root'
        if not isinstance(after.get('profiles'), dict) or not isinstance(after.get('compiled'), list) \
                or not isinstance((after.get('context') or {}).get('sources'), list):
            return None, 'receipt post-build snapshot lacks compiled/profile/source inventory'
    except (OSError, ValueError, UnicodeError) as error:
        return None, f'receipt unreadable: {error}'
    current, detail = run_receipt_verifier(verifier, attempt, limits)
    if not current:
        return None, f'stale or unverifiable receipt: {detail}'
    nodes = {n['name']: n for n in audit['nodes'] if isinstance(n, dict) and isinstance(n.get('name'), str)}
    theorems = {t['name']: t for t in audit['theorems'] if isinstance(t, dict) and isinstance(t.get('name'), str)}
    sources = {row['path']: source_sha(row) for row in after['context']['sources']
               if isinstance(row, dict) and isinstance(row.get('path'), str)}
    compiled_paths = {row['path'] for row in after['compiled'] if isinstance(row, dict) and isinstance(row.get('path'), str)}
    return {'attempt': str(attempt), 'root': Path(plan['root']), 'nodes': nodes, 'theorems': theorems, 'sources': sources,
            'compiled': compiled_paths, 'profiles': after['profiles'],
            'trust': {k: receipt.get(k) for k in ('authentication', 'source_correspondence', 'native_adequacy', 'proof_scope')}}, None


def module_of(relative):
    parts = Path(relative).with_suffix('').parts
    return '.'.join(parts) if all(IDENT.fullmatch(p) for p in parts) else None


def direct_reference(nodes, theorem, definition):
    """A statement about the root names it, so its own declaration depends on it directly.

    Requiring a direct edge (not transitive reachability) rejects theorems about wrappers
    or re-implementations that only reach the generated definition through other lemmas."""
    deps = nodes.get(theorem, {}).get('dependencies')
    return isinstance(deps, list) and definition in deps


def compiled_olean(bundle, module):
    suffix = '/.lake/build/lib/lean/' + module.replace('.', '/') + '.olean'
    return any(path.endswith(suffix) for path in bundle['compiled'])


def goal_rows(root, binding, reason):
    return [dict(goal, binding=binding, reason=reason, audited_theorem=None) for goal in root['goals']]


def bind_receipt(root, base, generated_sha, bundle, file_hashes):
    """Compiled status plus per-goal theorem bindings for one root."""
    if generated_sha is None:
        reason = 'no verified translation artifact; generated Lean cannot be bound to the receipt'
        return stage('not_run', reason), goal_rows(root, 'unbound', reason)
    matches = sorted(path for path, entry in bundle['profiles'].items()
                     if isinstance(entry, dict) and entry.get('sha256') == generated_sha)
    gen_modules = sorted({module_of(p) for p in matches} - {None})
    if not gen_modules:
        reason = 'source hash mismatch: receipt compiled no generated Lean byte-identical to the translation artifact'
        return stage('failed', reason), goal_rows(root, 'source_hash_mismatch', reason)
    contracts = {}
    for name in root['contracts']:
        # Lexical path: the receipt inventories (and Lean names) the tracked path, not a symlink target.
        path = base / name
        if not path.is_relative_to(bundle['root']):
            reason = f'contract {name} lies outside the receipt repository'
            return stage('failed', reason), goal_rows(root, 'unbound', reason)
        # Preflight already hashed every declared contract; unreadable ones have no hash.
        recorded = bundle['sources'].get(str(path))
        if recorded is None or recorded != file_hashes.get(name):
            reason = f'source hash mismatch: contract {name} differs from receipt source inventory'
            return stage('failed', reason), goal_rows(root, 'source_hash_mismatch', reason)
        contracts[name] = module_of(path.relative_to(bundle['root']))
    gen_modules = [m for m in gen_modules if compiled_olean(bundle, m)]
    missing = [name for name, m in contracts.items() if not m or not compiled_olean(bundle, m)]
    if not gen_modules or missing:
        reason = f'receipt compiled inventory lacks generated module or contracts {missing}'
        return stage('failed', reason), goal_rows(root, 'unbound', reason)
    compiled = stage('passed', 'current receipt compiled byte-identical generated Lean and declared contracts',
                     generated_modules=gen_modules, generated_paths=matches, receipt=bundle['attempt'])
    definition = root['namespace'] + '.' + root['function'].removeprefix(root['prefix'])
    contract_modules = set(contracts.values())
    goals = []
    for goal in root['goals']:
        name = next((n for n in (goal['theorem'], root['namespace'] + '.' + goal['theorem']) if n in bundle['theorems']), None)
        row = dict(goal, audited_theorem=name)
        theorem = bundle['theorems'].get(name)
        if theorem is None:
            row.update(binding='missing', reason='theorem absent from receipt audit')
        elif theorem.get('module') not in contract_modules:
            row.update(binding='outside_contracts', reason='theorem module is not a declared contract file')
        elif theorem.get('allowed') is not True or theorem.get('violations'):
            row.update(binding='policy_violation', reason='audited theorem violates dependency policy')
        elif (not direct_reference(bundle['nodes'], name, definition)
              or bundle['nodes'].get(definition, {}).get('module') not in gen_modules):
            row.update(binding='wrapper_or_unrelated',
                       reason=f'theorem does not directly reference generated root definition {definition} in {gen_modules}')
        else:
            row.update(binding='direct', reason='audited theorem depends on the hash-bound generated root definition',
                       audited_assumptions={k: sorted(theorem.get(k) or []) for k in
                                            ('axioms', 'opaque_dependencies', 'extern_dependencies', 'compiler_redirections')})
        goals.append(row)
    return compiled, goals


def diff_coverage(root, source_closure, file_hashes, summaries):
    if '.' not in root['function']:
        return stage('not_run', 'root function has no example.function form for differential binding'), []
    example, function = root['function'].rsplit('.', 1)
    counts, skipped = {}, []
    for path in summaries:
        try:
            summary = load_evidence(path)
            if not isinstance(summary, dict) or summary.get('schema') != 1 or summary.get('complete') is not True:
                return stage('failed', f'differential summary {path.name} is incomplete or unsupported'), []
            runner = summary.get('runner_runtime_sources')
            bound = [n for n in source_closure if n in file_hashes and isinstance(runner, dict) and n in runner]
            if not bound:
                return stage('failed', f'differential summary {path.name} does not hash any declared source-closure file'), []
            stale = [n for n in bound if runner[n] != file_hashes[n]]
            if stale:
                return stage('failed', f'stale differential evidence: source hash differs for {stale}'), []
            for line in read_bounded(Path(str(path) + '.jsonl'), 128 * 1024 * 1024).splitlines():
                row = bounded_json(line, LIMITS)
                if not isinstance(row, dict) or row.get('example') != example:
                    continue
                if row.get('status') == 'skipped' and function in (row.get('functions') or []):
                    skipped.append(row.get('reason'))
                elif row.get('function') == function and isinstance(row.get('status'), str):
                    counts[row['status']] = counts.get(row['status'], 0) + 1
        except (OSError, ValueError, UnicodeError) as error:
            return stage('failed', f'differential evidence unreadable: {error}'), []
    exclusions = [f'differential {s}: {counts[s]} sampled case(s)' for s in DIFF_EXCLUSIONS if counts.get(s)]
    exclusions += [f'differential example skipped: {r}' for r in skipped]
    total = sum(counts.values())
    if not total:
        return stage('not_run', 'no differential cases recorded for this root function', counts=counts), exclusions
    # Fail closed on statuses this reader does not know how to classify.
    failures = {s: n for s, n in counts.items() if s in DIFF_FAILURES or s not in DIFF_MATCHES + DIFF_EXCLUSIONS}
    if failures:
        return stage('failed', f'differential failures: {failures}', counts=counts, scope='sampled'), exclusions
    if not any(counts.get(s) for s in DIFF_MATCHES):
        return stage('failed', 'no differential case matched; only exclusions recorded', counts=counts, scope='sampled'), exclusions
    return stage('passed', 'all sampled differential cases matched or were classified exclusions',
                 counts=counts, scope='sampled'), exclusions


def coverage_level(record):
    stages, goals = record['stages'], record['goals']
    ok = {name: stages[name]['status'] == 'passed' for name in stages}
    direct = [g for g in goals if g['binding'] == 'direct']
    blockers = []
    if record['input_validation']['status'] != 'passed':
        blockers.append('declared inputs failed preflight')
    if not ok['translated']:
        blockers.append('translation not established by a hash-verified artifact')
    if not ok['compiled']:
        blockers.append('generated Lean not compiled by a current, hash-bound proof receipt')
    if not goals:
        blockers.append('no declared theorem goals')
    for goal in goals:
        if goal['binding'] != 'direct':
            blockers.append(f'goal {goal["theorem"]}: {goal["binding"]} ({goal["reason"]})')
    strengths = {g['strength'] for g in direct}
    if not strengths & set(FUNCTIONAL):
        blockers.append('no direct theorem has functional strength (partial/total correctness)')
    # Every functional precondition (preflight, translated, compiled, all goals direct) is a blocker above.
    functional = not blockers
    total = 'total_correctness' in strengths
    if strengths & set(FUNCTIONAL) and not total:
        blockers.append('termination not proved: only partial_correctness theorems are direct')
    if record['input_validation']['status'] != 'passed' or not ok['translated']:
        level = 'none'
    elif functional:
        level = 'functionally_verified_total' if total else 'functionally_verified_partial'
    elif not ok['compiled']:
        level = 'translated'
    elif direct:
        level = 'proved_scoped'
    elif ok['tested']:
        level = 'tested_sampled'
    else:
        level = 'compiled'
    return level, blockers


def coverage(path, artifact=None, receipt=None, verifier=None, diffs=()):
    manifest, limits, data, report = collect(path)
    base = path.parent
    file_hashes = {name.removeprefix('input/'): entry['sha256'] for name, entry in report['files'].items()
                   if name.startswith('input/')}
    generated, translated = {}, None
    if artifact is not None:
        try:
            verify(path, artifact)
            stored = load_evidence(path_under(artifact, 'report.json'))
            generated = {r['id']: stored['files'][f'generated/{r["id"]}/Gen.lean']['sha256'] for r in manifest['roots']}
            translated = stage('passed', 'translation artifact hashes match current inputs and translator',
                               artifact=str(artifact))
        except (OSError, ValueError, KeyError, TypeError, UnicodeError) as error:
            translated = stage('failed', f'stale or invalid translation artifact: {error}', artifact=str(artifact))
    bundle, receipt_error = (None, None)
    if receipt is not None:
        bundle, receipt_error = load_receipt(receipt, verifier, dict(limits, timeout_seconds=900))
    roots = []
    for root, evidence in zip(manifest['roots'], report['roots']):
        stages = {name: dict(evidence['stages'][name]) for name in STAGES}
        if translated is not None:
            stages['translated'] = translated
        if receipt is None:
            goals = goal_rows(root, 'no_receipt', 'no proof receipt supplied')
            stages['compiled'] = stage('not_run', 'no proof receipt supplied')
            stages['proved'] = stage('not_run', 'no proof receipt supplied')
        elif bundle is None:
            goals = goal_rows(root, 'stale_receipt', receipt_error)
            stages['compiled'] = stage('failed', receipt_error)
            stages['proved'] = stage('failed', receipt_error)
        else:
            stages['compiled'], goals = bind_receipt(root, base, generated.get(root['id']), bundle, file_hashes)
            bound = sum(g['binding'] == 'direct' for g in goals)
            if stages['compiled']['status'] != 'passed':
                stages['proved'] = stage(stages['compiled']['status'], stages['compiled']['reason'])
            elif goals and bound == len(goals):
                stages['proved'] = stage('passed', 'every declared goal is a direct audited theorem', direct_goals=bound)
            elif bound:
                stages['proved'] = stage('partial', f'{bound} of {len(goals)} declared goals are direct audited theorems', direct_goals=bound)
            else:
                stages['proved'] = stage('failed', 'no declared goal is a direct audited theorem of the generated root', direct_goals=0)
        diff_exclusions = []
        if diffs:
            stages['tested'], diff_exclusions = diff_coverage(root, manifest['source_closure'], file_hashes, diffs)
        else:
            stages['tested'] = stage('not_run', 'no differential summary supplied')
        audited = {}
        for goal in goals:
            for key, names in goal.get('audited_assumptions', {}).items():
                audited[key] = sorted(set(audited.get(key, [])) | set(names))
        exclusions = list(root['exclusions']) + diff_exclusions
        if bundle is not None:
            exclusions += [f'proof receipt {k}: {v}' for k, v in bundle['trust'].items() if v and v != 'selected compiled Lean theorem dependency policy only']
        record = {'id': root['id'], 'function': root['function'], 'input_validation': evidence['input_validation'],
                  'stages': stages, 'goals': goals,
                  'contract_domain': [{'theorem': g['theorem'], 'domain': g['domain'], 'review': 'declared_not_checked'} for g in root['goals']],
                  'theorem_strength': {'declared': sorted({g['strength'] for g in root['goals']}),
                                       'direct': sorted({g['strength'] for g in goals if g['binding'] == 'direct'}),
                                       'source': 'manifest declaration; statements are not machine-classified'},
                  'assumptions': {'declared': root['assumptions'], 'audited': audited},
                  'exclusions': exclusions}
        record['level'], record['blockers'] = coverage_level(record)
        record['fully_functionally_verified'] = record['level'] == 'functionally_verified_total'
        roots.append(record)
    return {'schema': SCHEMA, 'kind': 'air2lean-coverage-report', 'manifest_sha256': report['manifest_sha256'],
            'levels': list(LEVELS), 'roots': roots, 'diagnostics': report['diagnostics'],
            'rules': ['Sampled differential tests never raise a root above tested_sampled.',
                      'A theorem counts only when its own audited declaration (statement or proof term) directly references '
                      'the generated root definition in a module byte-identical to the verified translation artifact; '
                      'theorems reaching it only through wrappers or lemmas do not count. A wrapper statement whose proof '
                      'term mentions the root still counts, so declared strength and domain remain review obligations.',
                      'Functional verification requires every declared goal to be direct and at least one '
                      'partial/total correctness goal; full verification requires total_correctness.',
                      'Stale receipts, source hash mismatches and stale differential evidence fail their stages.'],
            'trust_scope': report['trust_scope']}


def coverage_text(result):
    lines = []
    for root in result['roots']:
        lines.append(f'{root["id"]} ({root["function"]}): {root["level"]}'
                     + (' [fully functionally verified]' if root['fully_functionally_verified'] else ''))
        for name in STAGES:
            entry = root['stages'][name]
            lines.append(f'  {name:<11} {entry["status"]:<8} {entry.get("reason", entry.get("code", ""))}')
        for goal in root['goals']:
            lines.append(f'  goal {goal["theorem"]} [{goal["strength"]}] domain: {goal["domain"]} -> {goal["binding"]}')
        lines.append(f'  assumptions: declared {root["assumptions"]["declared"]}; audited axioms '
                     f'{root["assumptions"]["audited"].get("axioms", [])}')
        lines.extend(f'  exclusion: {e}' for e in root['exclusions'])
        lines.extend(f'  blocker: {b}' for b in root['blockers'])
    return '\n'.join(lines) + '\n'


def reject_input_overlap(out, manifest_path, manifest):
    protected = {manifest_path} | {manifest_path.parent / name for name in input_names(manifest)}
    if out.resolve() in {p.resolve() for p in protected}:
        raise Invalid('report destination overlaps an input file')


# ---------------------------------------------------------------------------
# Reproducible project check (I03). From one committed manifest: translate, require
# byte-identical committed generated modules, build the contract modules with Lake under
# scripts/build-guard.py, audit them with scripts/assumptions.py, bind the audit to the
# declared goal theorems and their allowed assumptions, check declared strengths with
# scripts/claims.py, and write a record whose `reproducible` section another qualified
# machine must reproduce exactly (`compare-records`).

CHECK_DEFAULTS = {'build_timeout_seconds': 3600, 'audit_timeout_seconds': 3600, 'rss_mib': 8192}
CHECK_MAXIMA = {'build_timeout_seconds': 6 * 3600, 'audit_timeout_seconds': 6 * 3600, 'rss_mib': 64 * 1024}
STANDARD_AXIOMS = ('Classical.choice', 'Quot.sound', 'propext')
# Trust classes assigned by scripts/assumptions.py to project-policy dependencies. Standard
# library opaques/externs/redirections are disclosed but need no manifest entry; unexpected
# classes already make the audited theorem `allowed: false`.
PROJECT_TRUST = frozenset({'allowed-project-axiom', 'allowed-project-opaque',
                           'allowed-runtime-redirection', 'allowed-project-extern'})
TRUST_FIELDS = ('trust_class', 'compiler_trust_class', 'extern_trust_class')
CHECK_STAGES = ('translate', 'reproduce', 'build', 'audit', 'claims', 'inputs_stable')
RECORD_KIND = 'air2lean-project-check-record'
CHECK_TOOLS = {'project': Path(__file__).resolve()}
CHECK_TOOLS.update({key: CHECK_TOOLS['project'].with_name(name) for key, name in
                    (('build_guard', 'build-guard.py'), ('assumptions', 'assumptions.py'), ('claims', 'claims.py'))})


def check_budget(manifest):
    """Optional proof-checking budget: Lake build and audit timeouts, sampled RSS ceiling."""
    supplied = manifest.get('check', {})
    obj(supplied, (), CHECK_DEFAULTS)
    budget = dict(CHECK_DEFAULTS)
    for key, value in supplied.items():
        if type(value) is not int or not 1 <= value <= CHECK_MAXIMA[key]:
            raise Invalid(f'check.{key} must be an integer from 1 through {CHECK_MAXIMA[key]}')
        budget[key] = value
    return budget


def check_modules(manifest):
    """Contract and committed generated modules per root; every root must name both."""
    modules = {}
    for root in manifest['roots']:
        if 'generated' not in root:
            raise Invalid(f'check requires root {root["id"]} to declare its committed generated module')
        names = {'generated': module_of(root['generated']),
                 'contracts': [module_of(name) for name in root['contracts']]}
        if not names['contracts'] or None in names['contracts'] or names['generated'] is None:
            raise Invalid(f'root {root["id"]} needs Lean module paths for generated and at least one contract')
        modules[root['id']] = names
    return modules


def run_guarded(tools, base, staging, name, phase, timeout, budget, lock, command):
    """Run one Lake-backed stage under build-guard; the guard's JSON report is the evidence."""
    report_path, log_path = staging / f'{name}-guard.json', staging / f'{name}.log'
    argv = [sys.executable, str(tools['build_guard']), '--cwd', str(base), '--report', str(report_path),
            '--log', str(log_path), '--profile', 'project-check', '--phase', phase,
            '--timeout', str(timeout), '--rss-mib', str(budget['rss_mib']), '--log-bytes', str(16 * 1024 * 1024)]
    argv += ['--lock', str(lock)] if lock else []
    child = subprocess.Popen([*argv, '--', *command], cwd=base, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    try:
        _, stderr = child.communicate(timeout=timeout + 120)
    except BaseException:
        # The guard owns its workload's process tree: ask it to stop the tree, then wait.
        child.send_signal(signal.SIGTERM)
        try:
            child.wait(timeout=60)
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait()
        raise
    try:
        guard = json.loads(report_path.read_text())
        result = {'outcome': guard['outcome'], 'exit_code': guard['exit_code']}
    except (OSError, ValueError, KeyError, TypeError):
        detail = stderr.decode('utf-8', errors='replace').strip()[-2000:]
        return {'outcome': 'guard_error', 'exit_code': child.returncode, 'detail': detail}, {}
    return result, guard


def node_classes(node):
    return sorted({node.get(k) for k in TRUST_FIELDS if node.get(k)}) if node else ['unresolved']


def audit_goal(root, goal, theorems, nodes, modules):
    """Bind one declared goal to its audited theorem and confirm its assumptions are allowed."""
    name = next((n for n in (goal['theorem'], root['namespace'] + '.' + goal['theorem']) if n in theorems), None)
    row = {'theorem': goal['theorem'], 'audited_theorem': name, 'strength': goal['strength']}
    theorem = theorems.get(name)
    if theorem is None:
        return dict(row, status='missing', reason='goal theorem absent from the audit of the contract modules')
    if theorem.get('module') not in modules['contracts']:
        return dict(row, status='outside_contracts', reason=f'theorem module {theorem.get("module")} is not a declared contract')
    if theorem.get('allowed') is not True or theorem.get('violations'):
        return dict(row, status='policy_violation', violations=sorted(theorem.get('violations') or []),
                    reason='audited theorem violates the assurance dependency policy')
    used = set()
    for key in ('axioms', 'opaque_dependencies', 'extern_dependencies', 'compiler_redirections'):
        used.update(theorem.get(key) or [])
    standard, project = [], []
    for dep in sorted(used):
        node = nodes.get(dep)
        classes = node_classes(node)
        # Unknown nodes and non-standard axioms are never silently treated as standard.
        if dep in STANDARD_AXIOMS or (node and node.get('kind') != 'axiom' and not set(classes) & PROJECT_TRUST):
            standard.append(dep)
        else:
            project.append({'name': dep, 'classes': classes,
                            'policy_key': f'{node["module"]}::{node.get("user_name", dep)}' if node else None})
    declared = set(root['assumptions'])
    unallowed = [p['name'] for p in project if not {p['name'], p['policy_key']} & declared]
    definition = root['namespace'] + '.' + root['function'].removeprefix(root['prefix'])
    row.update(standard_assumptions=standard, project_assumptions=project,
               references_root=direct_reference(nodes, name, definition),
               root_definition_module=nodes.get(definition, {}).get('module'))
    if unallowed:
        return dict(row, status='unallowed_assumption', unallowed=unallowed,
                    reason='project assumptions absent from the root assumptions (and allowlist)')
    if row['root_definition_module'] != modules['generated']:
        return dict(row, status='unbound_generated',
                    reason=f'audited {definition} is not defined in the committed generated module {modules["generated"]}')
    return dict(row, status='allowed', reason=None)


def run_claims(tools, manifest_path, audit_path, staging):
    out = staging / 'claims.json'
    result = subprocess.run([sys.executable, str(tools['claims']), 'check', str(manifest_path),
                             '--assurance', str(audit_path), '--output', str(out)],
                            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=600)
    try:
        claims = load_evidence(out)
        goals = {f'{r["id"]}/{g["theorem"]}': {k: g.get(k) for k in ('status', 'declared_strength', 'derived_strength', 'claim_class', 'reason')}
                 for r in claims['roots'] for g in r['goals']}
    except (OSError, ValueError, UnicodeError, KeyError, TypeError):
        return {'status': 'error', 'exit_code': result.returncode,
                'reason': result.stderr.decode('utf-8', errors='replace').strip()[-2000:]}
    return {'status': claims.get('status'), 'exit_code': result.returncode, 'goals': goals}


def project_check(path, translator, staging, tools=None, lock=None):
    """Run the whole check into `staging`; stage failures are recorded, not raised."""
    tools = dict(CHECK_TOOLS, **(tools or {}))
    started = time.monotonic()
    manifest, limits, data, report = collect(path)
    budget = check_budget(manifest)
    modules = check_modules(manifest)
    base = path.parent
    failures = []
    inputs = dict(report['files'])
    toolchain = base / 'lean-toolchain'
    reproducible = {'manifest_sha256': report['manifest_sha256'], 'inputs': inputs, 'check_budget': budget,
                    'modules': modules,
                    'scripts': {key: hash_bounded(tool, 64 * 1024 * 1024)[0] for key, tool in sorted(tools.items())},
                    'lean_toolchain': toolchain.read_text().strip() if toolchain.is_file() else None,
                    'float_semantics': manifest['float_semantics'], 'spawn_policy': spawn_policy(manifest),
                    'stages': {name: {'status': 'not_run'} for name in CHECK_STAGES}, 'roots': []}
    stages = reproducible['stages']
    host = {'platform': {'system': platform.system(), 'machine': platform.machine(), 'release': platform.release()},
            'python': platform.python_version(), 'git': report['git'], 'manifest': str(path),
            'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    record = {'schema': SCHEMA, 'kind': RECORD_KIND, 'status': 'failed', 'failures': failures,
              'reproducible': reproducible, 'host': host,
              'note': 'compare-records compares only `reproducible`; `host` holds machine-specific '
                      'evidence (translator and Lake binaries, paths, timing, Git state).'}

    def finish():
        host['elapsed_seconds'] = round(time.monotonic() - started, 3)
        record['status'] = 'failed' if failures else 'reproduced'
        return record

    def translation_failed():
        stages['translate'] = {'status': 'failed', 'codes': sorted({d['code'] for d in report['diagnostics']})}
        failures.extend(f'translate {d["root"] or "project"}: {d["code"]}' for d in report['diagnostics'])
        return finish()

    if report['diagnostics']:
        return translation_failed()
    # 1. Translation into a hash-bound artifact, then re-verification of every recorded hash.
    artifact = staging / 'artifact'
    publish_translation(manifest, limits, data, report, translator, artifact)
    host['translator'] = report.get('translator')
    if report['diagnostics']:
        return translation_failed()
    try:
        verify(path, artifact)
    except (OSError, ValueError, UnicodeError) as error:
        stages['translate'] = {'status': 'failed', 'codes': ['ARTIFACT_VERIFY'], 'reason': str(error)}
        failures.append(f'translation artifact did not verify: {error}')
        return finish()
    generated = {root['id']: report['files'][f'generated/{root["id"]}/Gen.lean']['sha256'] for root in manifest['roots']}
    stages['translate'] = {'status': 'passed', 'generated_sha256': generated}
    # 2. The translation must reproduce the committed module that the contracts import.
    mismatched = [root['id'] for root in manifest['roots']
                  if inputs['input/' + root['generated']]['sha256'] != generated[root['id']]]
    stages['reproduce'] = {'status': 'failed' if mismatched else 'passed', 'mismatched_roots': mismatched}
    if mismatched:
        failures.append(f'fresh translation differs from committed generated module for {mismatched}')
        return finish()
    # 3. Build the contract modules (and their imports, including the generated modules).
    contract_modules = sorted({m for names in modules.values() for m in names['contracts']})
    stages['build'], guard = run_guarded(tools, base, staging, 'build', 'proof', budget['build_timeout_seconds'],
                                         budget, lock, ['lake', 'build', *contract_modules])
    stages['build']['status'] = 'passed' if stages['build']['outcome'] == 'success' else 'failed'
    host['build'] = {k: guard.get(k) for k in ('tools', 'pins', 'workload_seconds', 'peak_sampled_rss_kib', 'log_sha256')}
    if stages['build']['status'] != 'passed':
        failures.append(f'lake build failed: {stages["build"]["outcome"]}')
        return finish()
    # 4. Audit the just-built contract modules. assumptions.py exits 1 when any audited
    # theorem, possibly a non-goal one, violates policy; goal theorems are judged below.
    audit_path = staging / 'assumptions.json'
    audit_command = [sys.executable, str(tools['assumptions']), '--no-build', '--output', str(audit_path)]
    for module in contract_modules:
        audit_command += ['--module', module]
    stages['audit'], guard = run_guarded(tools, base, staging, 'audit', 'check', budget['audit_timeout_seconds'],
                                         budget, lock, audit_command)
    host['audit'] = {k: guard.get(k) for k in ('workload_seconds', 'peak_sampled_rss_kib', 'log_sha256')}
    try:
        if stages['audit']['outcome'] not in ('success', 'child_failed') or stages['audit']['exit_code'] not in (0, 1):
            raise Invalid(f'guard outcome {stages["audit"]["outcome"]}')
        audit = load_evidence(audit_path)
        if not isinstance(audit, dict) or audit.get('status') not in ('pass', 'fail') \
                or not isinstance(audit.get('theorems'), list) or not isinstance(audit.get('nodes'), list):
            raise Invalid('assurance report is not a completed audit')
        if audit.get('modules') != contract_modules:
            raise Invalid('assurance audit scope differs from the contract modules')
    except (OSError, ValueError, UnicodeError) as error:
        stages['audit'].update(status='failed', reason=str(error))
        failures.append(f'assumption audit failed: {error}')
        return finish()
    nodes = {n['name']: n for n in audit['nodes'] if isinstance(n, dict) and isinstance(n.get('name'), str)}
    theorems = {t['name']: t for t in audit['theorems'] if isinstance(t, dict) and isinstance(t.get('name'), str)}
    stages['audit'].update(status='passed', audit_status=audit['status'], theorem_count=len(audit['theorems']),
                           policy_sha256=audit.get('policy_sha256'), lean_toolchain=audit.get('lean_toolchain'))
    for root in manifest['roots']:
        goals = [audit_goal(root, goal, theorems, nodes, modules[root['id']]) for goal in root['goals']]
        reproducible['roots'].append({'id': root['id'], 'goals': goals})
        failures.extend(f'goal {root["id"]}/{g["theorem"]}: {g["status"]}' for g in goals if g['status'] != 'allowed')
    if not any(root['goals'] for root in manifest['roots']):
        failures.append('manifest declares no theorem goals')
    # 5. Declared strengths may not exceed the strength derived from audited theorem types.
    stages['claims'] = run_claims(tools, path, audit_path, staging)
    if stages['claims']['status'] != 'pass':
        failures.append(f'claim strength check: {stages["claims"]["status"]}')
    # 6. Inputs (manifest, sources, contracts, committed generated modules) unchanged throughout.
    after = collect(path)[3]['files']
    changed = sorted(name for name in set(inputs) | set(after) if inputs.get(name) != after.get(name))
    stages['inputs_stable'] = {'status': 'failed' if changed else 'passed', 'changed': changed}
    if changed:
        failures.append(f'inputs changed during check: {changed}')
    return finish()


def check_command(path, translator, out, tools=None, lock=None):
    """Publish a fresh directory: artifact, guard reports and logs, audit, claims, record.json."""
    out.parent.mkdir(parents=True, exist_ok=True)
    if out.exists():
        raise Invalid('check output already exists; choose a fresh directory')
    with tempfile.TemporaryDirectory(prefix='.air2lean-check-', dir=out.parent) as temp:
        staging = Path(temp) / 'check'
        staging.mkdir()
        record = project_check(path, translator, staging, tools, lock)
        encoded = report_bytes(record, LIMITS)
        (staging / 'record.json').write_bytes(encoded)
        if out.exists():
            raise Invalid('check output appeared during the run; refusing replacement')
        os.rename(staging, out)
    return record, encoded


def load_record(path):
    record = load_evidence(path)
    if not isinstance(record, dict) or record.get('schema') != SCHEMA or record.get('kind') != RECORD_KIND \
            or not isinstance(record.get('reproducible'), dict) or not isinstance(record.get('host', {}), dict):
        raise Invalid(f'{path} is not a schema-{SCHEMA} project check record')
    return record


def json_differences(left, right, where, found):
    if len(found) >= 200:
        return
    if isinstance(left, dict) and isinstance(right, dict):
        for key in sorted(set(left) | set(right)):
            json_differences(left.get(key, '<absent>'), right.get(key, '<absent>'), f'{where}.{key}', found)
    elif isinstance(left, list) and isinstance(right, list) and len(left) == len(right):
        for index, (a, b) in enumerate(zip(left, right)):
            json_differences(a, b, f'{where}[{index}]', found)
    elif left != right:
        found.append({'path': where, 'left': left, 'right': right})


def compare_records(left_path, right_path):
    left, right = load_record(left_path), load_record(right_path)
    differences = []
    json_differences(left['reproducible'], right['reproducible'], 'reproducible', differences)
    statuses = {'left': left.get('status'), 'right': right.get('status')}
    reproduced = not differences and all(s == 'reproduced' for s in statuses.values())
    return {'schema': SCHEMA, 'kind': 'air2lean-project-record-comparison',
            'status': 'reproduced' if reproduced else 'not_reproduced', 'record_status': statuses,
            'differences': differences, 'differences_truncated': len(differences) >= 200,
            'hosts': {'left': left.get('host', {}).get('platform'), 'right': right.get('host', {}).get('platform')}}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('report', 'translate', 'verify', 'coverage', 'check', 'compare-records'))
    parser.add_argument('manifest', type=Path, help='project manifest; compare-records: first check record')
    parser.add_argument('other', type=Path, nargs='?', help='compare-records: second check record')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--translator', type=Path)
    parser.add_argument('--artifact', type=Path)
    parser.add_argument('--overwrite', action='store_true', help='replace a report file; translation artifacts are immutable')
    parser.add_argument('--receipt', type=Path, help='coverage: proof receipt attempt directory')
    parser.add_argument('--receipt-verifier', type=Path, default=Path(__file__).resolve().with_name('proof-receipt.py'))
    parser.add_argument('--diff', type=Path, action='append', default=[], help='coverage: diff-report summary JSON')
    parser.add_argument('--format', choices=('json', 'text'), default='json')
    parser.add_argument('--require-level', choices=LEVELS, help='coverage: exit 1 if any root is below this level')
    parser.add_argument('--lock', type=Path, help='check: build-guard lock (default AIR2LEAN_BUILD_LOCK or the guard default)')
    parser.add_argument('--build-guard', type=Path, default=CHECK_TOOLS['build_guard'], help='check: build guard script')
    parser.add_argument('--assumptions-script', type=Path, default=CHECK_TOOLS['assumptions'], help='check: assurance audit script')
    parser.add_argument('--claims-script', type=Path, default=CHECK_TOOLS['claims'], help='check: claim strength script')
    args = parser.parse_args(argv)
    def cancel(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, cancel)
    try:
        if args.command == 'compare-records':
            if not args.other:
                raise Invalid('compare-records requires two check records')
            result = compare_records(args.manifest.resolve(), args.other.resolve())
            print(json.dumps(result, indent=2, sort_keys=True))
            return 0 if result['status'] == 'reproduced' else 1
        if args.command == 'check':
            if not args.out or not args.translator or args.overwrite:
                raise Invalid('check requires --out, --translator and no --overwrite; use a fresh record directory')
            tools = {'build_guard': args.build_guard.resolve(), 'assumptions': args.assumptions_script.resolve(),
                     'claims': args.claims_script.resolve()}
            record, encoded = check_command(args.manifest.resolve(), args.translator, args.out.resolve(), tools,
                                            args.lock and args.lock.resolve())
            print(encoded.decode('utf-8'), end='')
            return 0 if record['status'] == 'reproduced' else 1
        if args.command == 'coverage':
            result = coverage(args.manifest.resolve(), args.artifact and args.artifact.resolve(),
                              args.receipt, args.receipt_verifier.resolve(), [d.resolve() for d in args.diff])
            encoded = report_bytes(result, LIMITS)
            if args.out:
                reject_input_overlap(args.out, args.manifest.resolve(), load_manifest(args.manifest.resolve())[0])
                atomic_report(args.out, encoded, args.overwrite)
            print(coverage_text(result) if args.format == 'text' else encoded.decode('utf-8'), end='')
            if result['diagnostics']:
                return 1
            floor = LEVELS.index(args.require_level) if args.require_level else 0
            return 1 if any(LEVELS.index(r['level']) < floor for r in result['roots']) else 0
        if args.command == 'verify':
            if not args.artifact:
                raise Invalid('verify requires --artifact')
            print(json.dumps(verify(args.manifest.resolve(), args.artifact.resolve())))
            return 0
        manifest, limits, data, report = collect(args.manifest.resolve())
        if args.command == 'translate':
            if not args.out or not args.translator or args.overwrite:
                raise Invalid('translate requires --out, --translator and no --overwrite; use a fresh artifact directory')
            encoded = publish_translation(manifest, limits, data, report, args.translator, args.out.resolve())
        else:
            if args.out:
                reject_input_overlap(args.out, args.manifest.resolve(), manifest)
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
