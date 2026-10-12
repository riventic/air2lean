#!/usr/bin/env python3
"""Actions cache keys and hygiene (docs/ci.md#4-cache-hygiene).

  ci-cache.py zig-air-key VERSION [--host-pin TEXT]   cache key of one patched compiler build
  ci-cache.py prune [--dry-run]                        keep only the newest main entry per key prefix

`zig-air-key` hashes exactly what zig-patch/build.sh reads for VERSION: the exporter sources
(zig-patch/air-json/*.zig), the version's hook patch, build.sh, lock.sh, toml-get.sh and the
version's own versions.toml table (source URL, digest, hook, LLVM), plus the host-Zig pin that
bootstraps the build on this runner (its versions.toml table on Linux, the digest the macOS job
pins) and the runner OS/architecture. A pin change of another version does not change it.

`prune` (GH_TOKEN with actions:write, GITHUB_REPOSITORY) deletes every cache entry outside
refs/heads/main (PR and merge-queue scopes: only main saves) and every main entry but the newest
per prefix (the key without its trailing content hashes), so main stays far below the 10 GB limit
and none of its entries is evicted by size.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import urllib.parse
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
PATCH = 'zig-patch'


_spec = importlib.util.spec_from_file_location('air2lean_cas', ROOT / 'scripts/cas.py')
CAS = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(CAS)


def zig_air_key(root, version, host_pin=None, environ=os.environ):
    """scripts/cas.py zig_patch_inputs (what zig-patch/build.sh reads for VERSION) plus the
    host-Zig pin that bootstraps it on this runner."""
    root = Path(root)
    if host_pin is None:
        versions = (root / PATCH / 'versions.toml').read_text(encoding='utf-8')
        host_pin = '\n'.join(CAS.toml_table(versions, '[ci.host-zig."%s"]' % version))
    inputs = CAS.zig_patch_inputs(root, version)
    digest = hashlib.sha256(json.dumps({'inputs': inputs, 'host_pin': host_pin}, sort_keys=True).encode())
    host = '%s-%s' % (environ.get('RUNNER_OS', 'local'), environ.get('RUNNER_ARCH', 'local'))
    return 'zig-air-%s-%s-%s' % (host, version, digest.hexdigest())


def prefix(key):
    """The key without its trailing content hashes: `zig-air-Linux-X64-0.16.0-<hash>` -> `...-0.16.0`."""
    while True:
        shorter = re.sub(r'-[0-9a-f]{16,}$', '', key)
        if shorter == key:
            return key
        key = shorter


def plan_prune(entries):
    """The entries to delete: all outside main, and on main all but the newest per prefix."""
    newest = {}
    for entry in entries:
        if entry['ref'] != 'refs/heads/main':
            continue
        known = newest.get(prefix(entry['key']))
        if known is None or entry['created_at'] > known['created_at']:
            newest[prefix(entry['key'])] = entry
    keep = {entry['id'] for entry in newest.values()}
    return [entry for entry in entries if entry['id'] not in keep]


def api(method, path, token):
    request = urllib.request.Request(os.environ.get('GITHUB_API_URL', 'https://api.github.com') + path, method=method,
                                     headers={'Accept': 'application/vnd.github+json', 'Authorization': 'Bearer ' + token,
                                              'X-GitHub-Api-Version': '2022-11-28'})
    with urllib.request.urlopen(request, timeout=60) as response:
        body = response.read()
        return json.loads(body) if body else None


def prune(repository, token, dry_run=False):
    entries, page = [], 1
    while True:
        data = api('GET', '/repos/%s/actions/caches?per_page=100&page=%d' % (repository, page), token)
        entries += data.get('actions_caches', [])
        if len(data.get('actions_caches', [])) < 100:
            break
        page += 1
    doomed = plan_prune(entries)
    freed = sum(e['size_in_bytes'] for e in doomed)
    for entry in doomed:
        print('%s %s (%s, %d MB)' % ('would delete' if dry_run else 'delete', entry['key'], entry['ref'],
                                      entry['size_in_bytes'] // 2**20))
        if not dry_run:
            api('DELETE', '/repos/%s/actions/caches/%d' % (repository, entry['id']), token)
    kept = sum(e['size_in_bytes'] for e in entries) - freed
    print('%d of %d entries %s, %d MB freed, %d MB kept' % (len(doomed), len(entries),
          'to delete' if dry_run else 'deleted', freed // 2**20, kept // 2**20))
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--root', type=Path, default=ROOT)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('zig-air-key')
    p.add_argument('version')
    p.add_argument('--host-pin')
    p = sub.add_parser('prune')
    p.add_argument('--dry-run', action='store_true')
    args = parser.parse_args(argv)
    try:
        if args.command == 'zig-air-key':
            print(zig_air_key(args.root, args.version, args.host_pin))
            return 0
        return prune(os.environ['GITHUB_REPOSITORY'], os.environ['GH_TOKEN'], args.dry_run)
    except (OSError, ValueError, KeyError, StopIteration) as error:
        print('error: %s' % error, file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
