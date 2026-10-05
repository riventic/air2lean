#!/usr/bin/env python3
"""Observe a bounded Linux native ABI fragment; never widen translator support."""
import argparse
import hashlib
import json
import platform
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ('tests/roadmap/abi-probes/probe.zig', 'tests/diff/compat.zig')
TARGETS = ('x86_64-linux-gnu', 'aarch64-linux-gnu')
LAYOUTS = {'u9': [2, 2], 'u24': [4, 4], 'u40': [8, 8], 'u128': [16, 16],
           'pointer': [8, 8], 'packed32': [4, 4], 'vector4': [16, 16], 'record': [16, 8]}
VALUES = {'wrapping24': 1, 'packed_bits': 1793, 'vector_sum': 10, 'pointer_load': 1234567}
OFFSETS = {'record_count': 4, 'record_pointer': 8}


def fingerprints():
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in SOURCES}


def profile_check(profile):
    required = {'name', 'target_triple', 'pointer_bits', 'endian', 'abi', 'zig_version',
                'backend', 'cpu', 'features', 'build_mode', 'float_mode', 'error_set_bits',
                'error_layout', 'error_tracing', 'export_stage'}
    if not isinstance(profile, dict) or set(profile) != required:
        raise ValueError('expected an exact schema-12 raw source profile')
    if (profile['name'] != 'abi64-le-v1' or profile['target_triple'] not in TARGETS
            or type(profile['pointer_bits']) is not int or profile['pointer_bits'] != 64
            or profile['endian'] != 'little' or profile['abi'] != 'gnu'
            or profile['backend'] != 'stage2_llvm' or profile['zig_version'] != '0.16.0'
            or profile['build_mode'] not in ('ReleaseSafe', 'ReleaseFast')
            or profile['export_stage'] != 'analyzed-air'
            or profile['float_mode'] != 'per-instruction' or profile['error_layout'] != 'type-table'
            or type(profile['error_set_bits']) is not int or profile['error_set_bits'] != 16
            or type(profile['error_tracing']) is not bool):
        raise ValueError('unsupported source profile, backend, mode, endian or width')
    expected_cpu = 'x86_64' if profile['target_triple'].startswith('x86_64') else 'generic'
    if (profile['cpu'] != expected_cpu or not isinstance(profile['features'], list)
            or any(not isinstance(value, str) for value in profile['features'])
            or not profile['features'] or any(not value for value in profile['features'])
            or profile['features'] != sorted(set(profile['features']))):
        raise ValueError('probe requires baseline CPU and sorted unique feature names')


def observations(text, profile):
    data = {'meta': {}, 'layout': {}, 'offset': {}, 'value': {}, 'feature': {}}
    for line in text.splitlines():
        parts = line.split()
        if len(parts) < 3 or parts[0] not in data or parts[1] in data[parts[0]]:
            raise ValueError('malformed or duplicate probe observation')
        kind, name, *value = parts
        if kind == 'layout':
            if len(value) != 2:
                raise ValueError('invalid layout observation')
            data[kind][name] = list(map(int, value))
        else:
            if len(value) != 1:
                raise ValueError('invalid scalar observation')
            data[kind][name] = value[0] if kind == 'meta' else int(value[0])
    arch = profile['target_triple'].split('-')[0]
    expected_meta = {'arch': arch, 'os': 'linux', 'abi': 'gnu', 'endian': 'little',
                     'backend': profile['backend'], 'mode': profile['build_mode'],
                     'cpu': profile['cpu'], 'zig': profile['zig_version'], 'pointer_bits': '64', 'error_set_bits': '16',
                     'error_tracing': str(profile['error_tracing']).lower()}
    if data != {'meta': expected_meta, 'layout': LAYOUTS, 'offset': OFFSETS, 'value': VALUES,
                'feature': {name: 1 for name in profile['features']}}:
        raise ValueError('native observations differ from the bounded ABI contract: ' + json.dumps(data, sort_keys=True))
    return data


def run(zig, profile):
    profile_check(profile)
    if platform.system() != 'Linux':
        raise ValueError('actual probe execution requires a Linux validation environment')
    compiler = Path(zig).resolve(strict=True)
    if not compiler.is_file():
        raise ValueError('stock compiler must be a physical executable file')
    before = fingerprints()
    with tempfile.TemporaryDirectory(prefix='air2lean-abi-') as directory:
        binary = Path(directory) / 'probe'
        command = [str(compiler), 'build-exe', '-fllvm', '-O' + profile['build_mode'],
                   '-ferror-tracing' if profile['error_tracing'] else '-fno-error-tracing',
                   '-target', profile['target_triple'], '-mcpu=baseline', '-femit-bin=' + str(binary),
                   '--dep', 'compat', '-Mroot=' + str(ROOT / SOURCES[0]),
                   '-Mcompat=' + str(ROOT / SOURCES[1])]
        compiler_hash = hashlib.sha256(compiler.read_bytes()).hexdigest()
        subprocess.run(command, check=True, timeout=300, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        completed = subprocess.run([str(binary)], check=True, timeout=10,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if len(completed.stdout) > 16384:
            raise ValueError('oversized probe output')
        data = observations(completed.stdout.decode('utf-8'), profile)
        if fingerprints() != before or hashlib.sha256(compiler.read_bytes()).hexdigest() != compiler_hash:
            raise ValueError('probe inputs changed during observation')
        return {'schema': 1, 'kind': 'air2lean-native-abi-fragment', 'profile': profile,
                'source_sha256': before, 'compiler_sha256': compiler_hash,
                'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest(), 'command': command,
                'observations': data, 'scope': 'listed integer/pointer/layout observations only',
                'execution_host': {'system': platform.system(), 'machine': platform.machine()},
                'native_execution_attested': False,
                'float_abi_qualified': False, 'synchronization_qualified': False,
                'translation_qualified': False, 'wasm_qualified': False}


def compare(left, right):
    for report in (left, right):
        if report.get('schema') != 1 or report.get('kind') != 'air2lean-native-abi-fragment':
            raise ValueError('unsupported native report')
        profile_check(report['profile'])
        if report['source_sha256'] != fingerprints():
            raise ValueError('report does not bind current probe sources')
        # Imported JSON cannot attest execution. Revalidate every bounded observation.
        lines = []
        for kind, rows in report['observations'].items():
            for name, value in rows.items():
                fields = value if isinstance(value, list) else [value]
                lines.append(' '.join(map(str, [kind, name, *fields])))
        observations('\n'.join(lines), report['profile'])
    if {left['profile']['target_triple'], right['profile']['target_triple']} != set(TARGETS):
        raise ValueError('pair requires one observation of each selected Linux target')
    if left['profile']['build_mode'] != right['profile']['build_mode']:
        raise ValueError('pair build modes differ')
    return {'schema': 1, 'kind': 'air2lean-paired-abi-observations',
            'relation': 'exact equality of listed layouts, offsets and integer values',
            'observations_equal': all(left['observations'][key] == right['observations'][key]
                                      for key in ('layout', 'offset', 'value')),
            'native_execution_attested': False, 'translation_qualified': False, 'wasm_qualified': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    observe = sub.add_parser('observe')
    observe.add_argument('--zig', required=True)
    observe.add_argument('--profile', type=Path, required=True)
    observe.add_argument('--output', type=Path, required=True)
    pair = sub.add_parser('compare')
    pair.add_argument('left', type=Path)
    pair.add_argument('right', type=Path)
    args = parser.parse_args()
    if args.action == 'observe':
        report = run(args.zig, json.loads(args.profile.read_text()))
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    else:
        print(json.dumps(compare(json.loads(args.left.read_text()), json.loads(args.right.read_text())), indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError) as error:
        raise SystemExit('abi-probe: ' + str(error))
