#!/usr/bin/env python3
"""Whole-tree generated files: produced by CI on the exact merged tree, published on `generated`.

The files that assurance/generated.json lists describe the whole tree (coverage inventories,
premise index, provenance fixtures): they go stale whenever main moves, so they are not
committed (.gitignore). docs/ci.md#whole-tree-generated-files has the design and the trust
argument. This is the one helper that produces, publishes and supplies them:

  generated.py paths [--group G ...]            list the files
  generated.py regen [--group G ...]            regenerate them in the checkout (cheap groups by
                                                default; `--group provenance` needs zig-air-0.16.0,
                                                stock Zig 0.16.0 and Lean, like provenance-evidence.py)
  generated.py produce --out DIR [--group G ...]
                                                CI: regenerate twice, require identical output (up to
                                                the run-bound fields the registry names), keep the
                                                first in the checkout and copy it to DIR with
                                                DIR/generated-manifest.json (commit, tree, digests)
  generated.py install DIR ...                  verify produced directories against HEAD and copy them
                                                into the checkout
  generated.py fetch [--rev REV] [--group G ...]
                                                write the files published for main commit REV (default:
                                                the newest published first-parent ancestor of HEAD's
                                                merge base with origin/main) into the checkout
  generated.py materialize [--heavy fetch|regen|skip]
                                                local tools and preflight: regenerate the cheap groups,
                                                fetch (or regenerate, or skip) the heavy ones; offline the
                                                cheap groups still regenerate
  generated.py publish --repo OWNER/NAME [--push]
                                                CI on main: append one `generated` commit per main
                                                commit that has none, from the files its merge_group (or
                                                workflow_dispatch) run produced; nothing is regenerated
  generated.py freshness [--minutes N] [--repo OWNER/NAME]
                                                fail when a main commit older than N minutes has no entry

A `generated` commit's tree holds exactly the registry's files at their repository paths; its
message names the main commit, its tree and the CI run (trailers Main-Commit, Main-Tree, CI-Run).
"""
from __future__ import annotations

import argparse
import atexit
import calendar
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import tomllib
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = 'assurance/generated.json'
SCHEMA = 'air2lean-generated/1'
MANIFEST = 'generated-manifest.json'
WORKFLOW = '.github/workflows/ci.yml'
EVIDENCE_EVENTS = ('merge_group', 'workflow_dispatch')
REMOTE_REF = 'refs/remotes/origin/generated'


class Error(Exception):
    pass


def run(*args, cwd=ROOT, **kwargs):
    return subprocess.run([str(a) for a in args], cwd=cwd, check=True, **kwargs)


def git(*args, cwd=ROOT, check=True, env=None, input=None):
    result = subprocess.run(['git', *map(str, args)], cwd=cwd, capture_output=True, env=env, input=input)
    if check and result.returncode:
        raise Error('git %s: %s' % (' '.join(map(str, args)), result.stderr.decode(errors='replace').strip()))
    return result.stdout.decode().strip() if result.returncode == 0 else None


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(root: Path = ROOT) -> dict:
    data = json.loads((root / REGISTRY).read_text())
    if data.get('schema') != SCHEMA:
        raise Error('%s: unknown schema %r' % (REGISTRY, data.get('schema')))
    return data


def groups(data: dict, names=None) -> list[dict]:
    known = {g['name']: g for g in data['groups']}
    unknown = set(names or ()) - set(known)
    if unknown:
        raise Error('unknown group(s) %s (registry: %s)' % (', '.join(sorted(unknown)), ', '.join(known)))
    return [g for g in data['groups'] if not names or g['name'] in names]


def all_paths(data: dict, names=None) -> list[str]:
    return [p for g in groups(data, names) for p in g['paths']]


def paths(root: Path = ROOT) -> set[str]:
    """Every registry file of the tree at `root` (none without a registry): the one reader that
    check-tree.py, ci-reuse.py, artifact-manifest.py and the fixture tests share."""
    return set(all_paths(load(root))) if (Path(root) / REGISTRY).is_file() else set()


def cheap(data: dict) -> list[str]:
    """The groups that need no build (regenerated wherever the checkout is)."""
    return [g['name'] for g in data['groups'] if not g.get('heavy')]


# ----------------------------------------------------------------------------- generators

SOURCES = {}  # version -> extracted pristine source, shared by both passes of `produce`


def pinned_source(version: str, cache: Path) -> Path:
    """The pinned pristine compiler source of `version` (zig-patch/versions.toml), cached as
    zig-patch/build.sh caches it, extracted once per process."""
    if version in SOURCES:
        return SOURCES[version]
    pin = tomllib.loads((ROOT / 'zig-patch/versions.toml').read_text())[version]
    url, digest = pin['url'], pin['sha256']
    tarball = cache / ('zig-%s.tar.xz' % version)
    if not tarball.is_file() or sha256(tarball) != digest:
        cache.mkdir(parents=True, exist_ok=True)
        part = Path(tempfile.mkstemp(dir=cache, prefix=tarball.name + '.part.')[1])
        try:
            with urllib.request.urlopen(url, timeout=300) as response, part.open('wb') as out:
                shutil.copyfileobj(response, out)
            if sha256(part) != digest:
                raise Error('%s: sha256 differs from zig-patch/versions.toml' % url)
            os.replace(part, tarball)
        finally:
            part.unlink(missing_ok=True)
    source = Path(tempfile.mkdtemp(prefix='air2lean-zig-%s.' % version))
    atexit.register(shutil.rmtree, source, True)
    with tarfile.open(tarball) as archive:
        members = []
        for member in archive.getmembers():
            name = member.name.split('/', 1)
            if len(name) == 2 and (member.isfile() or member.isdir()):
                member.name = name[1]
                members.append(member)
        archive.extractall(source, members=members, filter='data')
    SOURCES[version] = source
    return source


def gen_coverage(group: dict, root: Path):
    cache = Path(os.environ.get('AIR2LEAN_CACHE', Path.home() / '.cache/air2lean'))

    def one(rel):
        version = Path(rel).stem
        run(sys.executable, '-B', 'scripts/coverage.py', 'generate', '--version', version,
            '--source', pinned_source(version, cache), '--os', 'linux', '--inventory', rel, cwd=root)
    with concurrent.futures.ThreadPoolExecutor() as pool:  # one coverage.py process per version
        list(pool.map(one, group['paths']))


def gen_premise_index(group: dict, root: Path):
    run(sys.executable, '-B', 'scripts/premises.py', 'write', cwd=root)


def gen_provenance(group: dict, root: Path):
    with tempfile.TemporaryDirectory() as scratch:
        work = Path(scratch).resolve() / 'work'  # the receipt refuses a path through a symlink (macOS /var)
        tool = [sys.executable, '-B', 'scripts/provenance-evidence.py', '--fixture', group['fixture']]
        run(*tool, 'regenerate', work, '--refresh', cwd=root)
        run(*tool, 'install', work, cwd=root)
        # The receipt `install` just wrote is untracked by design; it was produced from HEAD here.
        run(*tool, 'record', work, '--generated-from-head', cwd=root)


GENERATORS = {'coverage': gen_coverage, 'premise-index': gen_premise_index, 'provenance': gen_provenance}


def regen(data: dict, names=None, root: Path = ROOT):
    for group in groups(data, names):
        for rel in group['paths']:
            (root / rel).unlink(missing_ok=True)
        print('== regenerating %s' % group['name'], flush=True)
        GENERATORS[group['generator']](group, root)
        missing = [rel for rel in group['paths'] if not (root / rel).is_file()]
        if missing:
            raise Error('%s: the generator wrote no %s' % (group['name'], ', '.join(missing)))


# ----------------------------------------------------------------------------- produce / install

def drop(value, dotted: str):
    """`value` without the field at the dotted path (absent paths are fine)."""
    head, _, rest = dotted.partition('.')
    if not isinstance(value, dict) or head not in value:
        return value
    value = dict(value)
    if rest:
        value[head] = drop(value[head], rest)
    else:
        del value[head]
    return value


def comparable(data: dict, rel: str, path: Path) -> bytes:
    """The bytes the determinism check compares: the file, without the fields that bind one
    particular run (a receipt's guard report and log digests, and what chains them)."""
    fields = next((g.get('run_bound', {}).get(rel) for g in data['groups'] if rel in g['paths']), None)
    if not fields:
        return path.read_bytes()
    value = json.loads(path.read_text())
    for field in fields:
        value = drop(value, field)
    return json.dumps(value, sort_keys=True).encode()


def differences(a: Path, b: Path) -> list[str]:
    """The dotted JSON paths (or `bytes`) at which two regenerations of a file differ."""
    def flat(value, prefix=''):
        if isinstance(value, dict):
            for key, item in value.items():
                yield from flat(item, prefix + '.' + key)
        elif isinstance(value, list):
            for index, item in enumerate(value):
                yield from flat(item, '%s[%d]' % (prefix, index))
        else:
            yield prefix, value
    try:
        left, right = dict(flat(json.loads(a.read_text()))), dict(flat(json.loads(b.read_text())))
    except ValueError:
        return ['bytes']
    return ['%s: %.60r | %.60r' % (k, left.get(k), right.get(k)) for k in sorted(set(left) | set(right))
            if left.get(k) != right.get(k)]


def head_identity(root: Path = ROOT) -> dict:
    return {'commit': git('rev-parse', 'HEAD^{commit}', cwd=root), 'tree': git('rev-parse', 'HEAD^{tree}', cwd=root)}


def produce(data: dict, names, out: Path, root: Path = ROOT):
    """Regenerate twice; the passes must agree. The first pass's files stay in the checkout."""
    paths = all_paths(data, names)
    passes = []
    for number in (1, 2):
        regen(data, names, root)
        snapshot = out.parent / ('.%s.pass%d' % (out.name, number))
        shutil.rmtree(snapshot, ignore_errors=True)
        for rel in paths:
            (snapshot / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(root / rel, snapshot / rel)
        passes.append(snapshot)
    differ = [rel for rel in paths
              if comparable(data, rel, passes[0] / rel) != comparable(data, rel, passes[1] / rel)]
    if differ:
        for rel in differ:
            print('%s differs:\n  %s' % (rel, '\n  '.join(differences(passes[0] / rel, passes[1] / rel)[:20])),
                  file=sys.stderr)
        raise Error('not deterministic: two regenerations on the same tree differ in %s' % ', '.join(differ))
    shutil.rmtree(out, ignore_errors=True)
    shutil.copytree(passes[0], out)
    for rel in paths:
        shutil.copy2(passes[0] / rel, root / rel)
    for snapshot in passes:
        shutil.rmtree(snapshot)
    manifest = {'schema': SCHEMA, **head_identity(root), 'groups': [g['name'] for g in groups(data, names)],
                'files': {rel: sha256(out / rel) for rel in paths}}
    (out / MANIFEST).write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print('produced %d files for %s (tree %s), deterministic over two regenerations'
          % (len(paths), manifest['commit'], manifest['tree']))


def verified(directory: Path, data: dict, commit: str, tree: str) -> dict:
    """The manifest of a produced directory, checked against the expected commit and tree and
    the files' digests; the groups must be registry groups with exactly their paths."""
    manifest = json.loads((directory / MANIFEST).read_text())
    if manifest.get('schema') != SCHEMA:
        raise Error('%s: unknown schema' % directory)
    if (manifest.get('commit'), manifest.get('tree')) != (commit, tree):
        raise Error('%s: produced for commit %s tree %s, not commit %s tree %s'
                    % (directory, manifest.get('commit'), manifest.get('tree'), commit, tree))
    expected = all_paths(data, manifest.get('groups') or ['-'])
    if sorted(manifest.get('files', {})) != sorted(expected):
        raise Error('%s: files %s are not exactly those of groups %s'
                    % (directory, sorted(manifest.get('files', {})), manifest.get('groups')))
    for rel, digest in manifest['files'].items():
        if sha256(directory / rel) != digest:
            raise Error('%s: %s does not match its recorded digest' % (directory, rel))
    return manifest


def install(data: dict, directories, root: Path = ROOT):
    identity = head_identity(root)
    for directory in directories:
        manifest = verified(Path(directory), data, identity['commit'], identity['tree'])
        for rel in manifest['files']:
            (root / rel).parent.mkdir(parents=True, exist_ok=True)
            (root / rel).write_bytes((Path(directory) / rel).read_bytes())
        print('installed %s (%s) for %s' % (directory, ', '.join(manifest['groups']), identity['commit']))


# ----------------------------------------------------------------------------- the generated branch

def fetch_branch(data: dict, root: Path = ROOT) -> bool:
    branch = data['branch']
    done = subprocess.run(['git', 'fetch', '--quiet', '--no-tags', 'origin',
                           '+refs/heads/%s:%s' % (branch, REMOTE_REF)], cwd=root, capture_output=True)
    if done.returncode:
        print('could not fetch the %s branch: %s' % (branch, done.stderr.decode(errors='replace').strip()),
              file=sys.stderr)
    return git('rev-parse', '--verify', '--quiet', REMOTE_REF, cwd=root, check=False) is not None


def entries(root: Path = ROOT, ref: str = REMOTE_REF) -> dict:
    """{main commit: generated commit} of every entry on the branch."""
    if git('rev-parse', '--verify', '--quiet', ref, cwd=root, check=False) is None:
        return {}
    out = git('log', '--format=%H %(trailers:key=Main-Commit,valueonly,separator=)', ref, cwd=root)
    found = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 2:
            found.setdefault(parts[1], parts[0])
    return found


def fetch(data: dict, names, rev: str | None, root: Path = ROOT) -> str:
    if not fetch_branch(data, root):
        raise Error('no %s branch available (offline?): regenerate with scripts/generated.py regen' % data['branch'])
    published = entries(root)
    if rev:
        commit = git('rev-parse', rev + '^{commit}', cwd=root)
        candidates = [commit]
    else:
        base = git('merge-base', 'HEAD', 'origin/main', cwd=root, check=False) or 'HEAD'
        candidates = git('rev-list', '--first-parent', '--max-count=200', base, cwd=root).split()
    commit = next((c for c in candidates if c in published), None)
    if commit is None:
        raise Error('no published entry for %s' % (rev or 'any first-parent ancestor of the merge base'))
    entry = published[commit]
    for rel in all_paths(data, names):
        blob = subprocess.run(['git', 'cat-file', 'blob', '%s:%s' % (entry, rel)], cwd=root, capture_output=True)
        if blob.returncode:
            raise Error('%s (entry %s for %s) has no %s' % (data['branch'], entry, commit, rel))
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        (root / rel).write_bytes(blob.stdout)
    print('fetched %s from %s entry %s (main %s)' % (', '.join(g['name'] for g in groups(data, names)),
                                                   data['branch'], entry[:12], commit[:12]))
    return commit


def materialize(data: dict, heavy: str, root: Path = ROOT):
    regen(data, cheap(data), root)
    rest = [g['name'] for g in data['groups'] if g.get('heavy')]
    if heavy == 'regen':
        regen(data, rest, root)
    elif heavy == 'fetch':
        try:
            commit = fetch(data, rest, None, root)
            print('note: %s are main %s\'s; CI regenerates them for this tree' % (', '.join(rest), commit[:12]))
        except Error as error:
            print('note: %s not materialized (%s); CI regenerates them' % (', '.join(rest), error), file=sys.stderr)


def api(path: str):
    """`gh api` (the publish workflow needs `gh run download` anyway)."""
    done = subprocess.run(['gh', 'api', path], capture_output=True, text=True)
    if done.returncode:
        raise Error('gh api %s: %s' % (path, done.stderr.strip()))
    return json.loads(done.stdout) if done.stdout.strip() else None


def pending(root: Path, published: dict, head: str = 'origin/main') -> list[str]:
    """First-parent main commits since the registry exists that have no entry, oldest first.
    Walking back stops at the newest published commit."""
    found = []
    for commit in git('rev-list', '--first-parent', '--max-count=500', head, cwd=root).split():
        if commit in published or git('cat-file', '-e', '%s:%s' % (commit, REGISTRY), cwd=root, check=False) is None:
            break
        found.append(commit)
    return found[::-1]


def evidence_run(repo: str, commit: str) -> dict | None:
    """The newest successful CI run of an evidence event (merge_group, workflow_dispatch) for `commit`."""
    runs = api('repos/%s/actions/runs?head_sha=%s&status=success&per_page=100' % (repo, commit))['workflow_runs']
    runs = [r for r in runs if r['path'].split('@')[0] == WORKFLOW and r['event'] in EVIDENCE_EVENTS
            and r['head_sha'] == commit and (r.get('head_repository') or {}).get('full_name') == repo]
    return max(runs, key=lambda r: r['run_started_at'], default=None)


def entry_commit(data: dict, directories, commit: str, tree: str, run_: dict, parent: str | None,
                 root: Path = ROOT) -> str:
    """The `generated` commit for main `commit`: its tree is exactly the registry's files from the
    produced `directories` (each verified against `commit` and `tree`), its parent the previous entry."""
    manifests = [verified(Path(d), data, commit, tree) for d in directories]
    covered = sorted(p for m in manifests for p in m['files'])
    if covered != sorted(all_paths(data)):
        raise Error('run %s produced %s, not every registry file' % (run_['id'], covered))
    bot = 'github-actions[bot]', '41898282+github-actions[bot]@users.noreply.github.com'
    with tempfile.TemporaryDirectory() as scratch:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(scratch) / 'index'),
                   GIT_AUTHOR_NAME=bot[0], GIT_COMMITTER_NAME=bot[0], GIT_AUTHOR_EMAIL=bot[1], GIT_COMMITTER_EMAIL=bot[1])
        for directory, manifest in zip(directories, manifests):
            for rel in manifest['files']:
                blob = git('hash-object', '-w', Path(directory) / rel, cwd=root)
                git('update-index', '--add', '--cacheinfo', '100644,%s,%s' % (blob, rel), cwd=root, env=env)
        entry_tree = git('write-tree', cwd=root, env=env)
    message = ('Generated files for main %s\n\nProduced twice by CI run %s (%s) on the merged tree; '
               'not regenerated here.\n\nMain-Commit: %s\nMain-Tree: %s\nCI-Run: %s\n'
               % (commit[:12], run_['id'], run_['event'], commit, tree, run_['html_url']))
    parents = ['-p', parent] if parent else []
    return git('commit-tree', entry_tree, *parents, cwd=root, env=env, input=message.encode())


def publish(data: dict, repo: str, push: bool, root: Path = ROOT):
    fetch_branch(data, root)
    published = entries(root)
    todo = pending(root, published)
    if not todo:
        print('every main commit since %s exists has its %s entry' % (REGISTRY, data['branch']))
        return 0
    tip = git('rev-parse', '--verify', '--quiet', REMOTE_REF, cwd=root, check=False)
    for commit in todo:
        run_ = evidence_run(repo, commit)
        if run_ is None:
            # Entries stay in main's order; the freshness check reports a gap that persists.
            print('main %s: no successful merge_group/workflow_dispatch CI run yet; not published' % commit,
                  file=sys.stderr)
            break
        tree = git('rev-parse', commit + '^{tree}', cwd=root)
        with tempfile.TemporaryDirectory() as scratch:
            directories = []
            for name in ('generated-files', 'generated-provenance'):
                target = Path(scratch) / name
                run('gh', 'run', 'download', run_['id'], '--repo', repo, '--name', name, '--dir', target)
                directories.append(target)
            tip = entry_commit(data, directories, commit, tree, run_, tip, root)
        print('main %s -> %s %s (run %s)' % (commit[:12], data['branch'], tip[:12], run_['id']))
    if tip and push:
        run('git', 'push', 'origin', '%s:refs/heads/%s' % (tip, data['branch']))
    return 0


def landing_times(repo: str | None) -> dict:
    """{main commit: epoch seconds when a push made it main's head}, from the repository activity
    API; commits it does not cover fall back to their committer date."""
    if not repo:
        return {}
    times = {}
    try:
        activity = api('repos/%s/activity?ref=refs/heads/main&per_page=100' % repo)
    except Error as error:
        print('note: no repository activity (%s); using committer dates' % error, file=sys.stderr)
        return {}
    for item in activity:
        stamp = calendar.timegm(time.strptime(item['timestamp'], '%Y-%m-%dT%H:%M:%SZ'))
        span = git('rev-list', '--first-parent', '%s..%s' % (item['before'], item['after']), check=False) \
            if set(item['before']) != {'0'} else item['after']
        for commit in (span or '').split():
            times[commit] = min(times.get(commit, stamp), stamp)
    return times


def freshness(data: dict, minutes: int, repo: str | None, root: Path = ROOT) -> int:
    fetch_branch(data, root)
    published = entries(root)
    landed = landing_times(repo)
    now = time.time()
    stale = []
    for commit in pending(root, published):
        when = landed.get(commit) or int(git('show', '-s', '--format=%ct', commit, cwd=root))
        if now - when > minutes * 60:
            stale.append('%s (main for %d min)' % (commit, (now - when) // 60))
    if stale:
        print('error: main commits without a %s entry after %d minutes (docs/ci.md#whole-tree-generated-files):\n  %s'
              % (data['branch'], minutes, '\n  '.join(stale)), file=sys.stderr)
        return 1
    print('fresh: every main commit older than %d minutes has its %s entry' % (minutes, data['branch']))
    return 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('paths', 'regen', 'produce', 'fetch'):
        p = sub.add_parser(name)
        p.add_argument('--group', action='append', dest='groups')
    sub.choices['produce'].add_argument('--out', type=Path, required=True)
    sub.choices['fetch'].add_argument('--rev')
    p = sub.add_parser('install')
    p.add_argument('directories', nargs='+', type=Path)
    p = sub.add_parser('materialize')
    p.add_argument('--heavy', choices=('fetch', 'regen', 'skip'), default='fetch')
    p = sub.add_parser('publish')
    p.add_argument('--repo', required=True)
    p.add_argument('--push', action='store_true')
    p = sub.add_parser('freshness')
    p.add_argument('--minutes', type=int)
    p.add_argument('--repo')
    args = parser.parse_args(argv)
    try:
        data = load()
        if args.command == 'paths':
            print('\n'.join(all_paths(data, args.groups)))
        elif args.command == 'regen':
            regen(data, args.groups or cheap(data))
        elif args.command == 'produce':
            produce(data, args.groups, args.out.resolve())
        elif args.command == 'install':
            install(data, args.directories)
        elif args.command == 'fetch':
            fetch(data, args.groups, args.rev)
        elif args.command == 'materialize':
            materialize(data, args.heavy)
        elif args.command == 'publish':
            return publish(data, args.repo, args.push)
        elif args.command == 'freshness':
            return freshness(data, args.minutes or data['freshness_minutes'], args.repo)
    except (Error, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print('generated: %s' % error, file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
