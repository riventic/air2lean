#!/usr/bin/env python3
"""Opt-in Docker check of the restricted row's process-memory boundary.

Set AIR2LEAN_RUN_DOCKER_BOUNDARY=1 under the normal build guard to execute it.
The same image must also expose actual retained source/history archives; denied
or inactive readers therefore cannot turn the negative check green.
This checks the process-memory boundary on a native ARM Docker engine only;
it does not qualify production Zig/Lean native execution or other platforms.
"""
import hashlib
import json
import os
import secrets
import signal
import subprocess
import unittest

import test_cache as fixtures

ROOT, runner = fixtures.ROOT, fixtures.runner


SCANNER = r'''import argparse,hashlib,io,json,os,subprocess,tarfile,zlib
from pathlib import Path

prefix=b'air2lean-withheld-memory-'
marker_length=__MARKER_LENGTH__
marker_digest='__MARKER_DIGEST__'
parser=argparse.ArgumentParser()
parser.add_argument('--positive',action='store_true')
parser.add_argument('--out')
parser.add_argument('--archive-specs',default='{}')
args=parser.parse_args()
specs=json.loads(args.archive_specs)
for spec in specs.values():
    spec['prefix_bytes']=bytes.fromhex(spec['prefix_hex'])

def marker_matches(value):
    return (len(value)==marker_length and value.startswith(prefix) and
            hashlib.sha256(value).hexdigest()==marker_digest)

def raw_marker(data):
    start=0
    while True:
        start=data.find(prefix,start)
        if start<0:
            return False
        if marker_matches(data[start:start+marker_length]):
            return True
        start+=1

def compressed_marker(data):
    # Git pack blobs use zlib; gzip covers a compressed source tar. The tiny
    # fixture's individual inflated objects fit within this explicit bound.
    for signature,wbits in ((b'\x1f\x8b\x08',31),(b'\x78\x01',15),
                            (b'\x78\x5e',15),(b'\x78\x9c',15),(b'\x78\xda',15)):
        start=0
        while True:
            start=data.find(signature,start)
            if start<0:
                break
            try:
                decoder=zlib.decompressobj(wbits)
                expanded=decoder.decompress(data[start:],1024*1024)
                if raw_marker(expanded):
                    return True
            except zlib.error:
                pass
            start+=1
    return False

def archive_marker(name,data):
    if name=='source':
        try:
            with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as archive:
                member=archive.extractfile('withheld-marker.txt')
                return member is not None and marker_matches(member.read(marker_length+1))
        except (tarfile.TarError,KeyError,OSError):
            return False
    return (data.startswith((b'# v2 git bundle\n',b'# v3 git bundle\n')) and
            b'\n\nPACK' in data and compressed_marker(data))

def scan(pid):
    result={'pid':pid,'bytes_read':0,'found':False,'compressed_found':False,
            'errors':[],'excluded_kernel_maps':[],'budget_exhausted':False,
            'archives':{name:{'found':False,'marker_recovered':False} for name in specs}}
    try:
        result['cmdline']=Path(f'/proc/{pid}/cmdline').read_bytes().decode(errors='replace').split('\0')
        regions=Path(f'/proc/{pid}/maps').read_text().splitlines()
    except OSError as error:
        result['errors'].append({'operation':'maps','mapping':'<process metadata>',
                                 'errno':error.errno,'message':str(error)})
        return result
    try:
        memory=open(f'/proc/{pid}/mem','rb',buffering=0)
    except OSError as error:
        result['errors'].append({'operation':'mem-open','mapping':'<all mappings>',
                                 'errno':error.errno,'message':str(error)})
        return result
    with memory:
        for region in regions:
            address,permissions,*_rest=region.split()
            if not permissions.startswith('r'):
                continue
            label=' '.join(_rest[3:]) or '<anonymous>'
            # These kernel-owned pages cannot hold a Python/source allocation and
            # Linux does not expose them through /proc/PID/mem on every kernel.
            if label in ('[vvar]','[vvar_vclock]','[vsyscall]'):
                result['excluded_kernel_maps'].append({'mapping':label,'address':address})
                continue
            start,end=(int(value,16) for value in address.split('-'))
            position,tail=start,b''
            while position<end:
                room=256*1024*1024-result['bytes_read']
                if room<=0:
                    result['budget_exhausted']=True
                    return result
                try:
                    memory.seek(position)
                    chunk=memory.read(min(1024*1024,end-position,room))
                    if not chunk:
                        raise OSError('empty mapped-memory read')
                except (OSError,OverflowError,ValueError) as error:
                    result['errors'].append({'operation':'mem-read','mapping':label,'address':address,
                                             'errno':getattr(error,'errno',None),'message':str(error)})
                    break
                result['bytes_read']+=len(chunk)
                window=tail+chunk
                if raw_marker(window):
                    result['found']=True
                if compressed_marker(window):
                    result['compressed_found']=True
                for name,spec in specs.items():
                    if result['archives'][name]['found']:
                        continue
                    start=0
                    while True:
                        start=window.find(spec['prefix_bytes'],start)
                        if start<0:
                            break
                        remaining=256*1024*1024-result['bytes_read']
                        if spec['length']>remaining:
                            result['budget_exhausted']=True
                            return result
                        try:
                            memory.seek(position-len(tail)+start)
                            candidate=memory.read(spec['length'])
                            result['bytes_read']+=len(candidate)
                            if hashlib.sha256(candidate).hexdigest()==spec['sha256']:
                                result['archives'][name]={'found':True,
                                    'marker_recovered':archive_marker(name,candidate)}
                                break
                        except (OSError,OverflowError,ValueError) as error:
                            result['errors'].append({'operation':'archive-read','mapping':label,
                                                     'address':address,'message':str(error)})
                        start+=1
                # Keep a complete bounded compressed candidate across chunk edges.
                tail=window[-(1024*1024-1):]
                position+=len(chunk)
    return result

report={'self_pid':os.getpid(),'parent':scan(os.getppid()),'pid1':scan(1)}
if args.positive:
    passed=(set(specs)=={'source','history'} and
            all(report[role]['bytes_read']>0 and not report[role]['errors'] and
                not report[role]['budget_exhausted'] and
                all(value['found'] and value['marker_recovered']
                    for value in report[role]['archives'].values()) for role in ('parent','pid1')))
else:
    snapshot=Path(os.environ.get('AIR2LEAN_LOCAL_SNAPSHOT','/snapshot'))
    report['archives']={str(snapshot/name):os.path.lexists(snapshot/name)
                        for name in ('source.tar','files','bootstrap.sh')}
    objects=subprocess.run(['git','cat-file','--batch-all-objects','--batch'],capture_output=True)
    report['git_objects']={'returncode':objects.returncode,'bytes_read':len(objects.stdout),
                           'found':raw_marker(objects.stdout),'stderr':objects.stderr.decode(errors='replace')}
    passed=(all(report[role]['bytes_read']>0 and not report[role]['errors'] and not report[role]['found'] and
                not report[role]['compressed_found'] and not report[role]['budget_exhausted']
                for role in ('parent','pid1')) and
            not any(report['archives'].values()) and objects.returncode==0 and
            not report['git_objects']['found'])
text=json.dumps(report,sort_keys=True)
if args.out:
    Path(args.out).write_text(text+'\n')
print(text,flush=True)
raise SystemExit(0 if passed else 1)
'''


@unittest.skipUnless(os.environ.get('AIR2LEAN_RUN_DOCKER_BOUNDARY') == '1',
                     'opt-in actual Docker boundary check')
class ProcessMemoryBoundary(unittest.TestCase):
    def docker(self, *arguments, check=True):
        return subprocess.run(['docker', *arguments], check=check, capture_output=True,
                              text=True, timeout=120)

    def container_id(self, path):
        value = path.read_text().strip()
        self.assertRegex(value, r'^[0-9a-f]{64}$')
        return value

    def remove_owned_container(self, path):
        if not path.exists():
            return
        identifier = self.container_id(path)
        result = self.docker('rm', '-f', identifier, check=False)
        if result.returncode:
            self.assertIn('no such', result.stderr.lower(), result.stderr)
            self.assertIn(identifier, result.stderr)

    def remove_run_containers(self, results):
        for path in results.glob('run.*/containers/*.id'):
            self.remove_owned_container(path)

    def wrapper(self, fixture, results):
        environment = dict(os.environ, AIR2LEAN_LOCAL_RESULTS=str(results), AIR2LEAN_LOCAL_TIMEOUT='5m')
        with subprocess.Popen(['bash', str(fixture.repo / 'scripts/local-ci.sh'), 'part', 'consumer'],
                              env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              start_new_session=True) as process:
            try:
                stdout, stderr = process.communicate(timeout=900)
            finally:
                if process.returncode is None:
                    runner.stop_group(process, signal.SIGTERM)
        self.assertEqual(process.returncode, 0, (stdout + stderr).decode(errors='replace'))

    def test_fresh_rows_withhold_memory_and_same_image_positive_control_finds_it(self):
        architecture = self.docker('info', '--format', '{{.Architecture}}').stdout.strip()
        self.assertIn(architecture, ('aarch64', 'arm64'),
                      'the process-memory boundary control requires a native ARM Docker engine')
        fixture = fixtures.Capture()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        fixture.part_fixture()
        for name in ('local-ci.sh', 'local-ci-steps.py', 'zig-default.sh', 'rosetta.sh'):
            fixture.write('scripts/' + name, (ROOT / 'scripts' / name).read_bytes())
        for name in ('Dockerfile.local-ci', 'lake-manifest.json', 'tests/diff/lean-toolchain',
                     'tests/diff/lake-manifest.json'):
            fixture.write(name, (ROOT / name).read_bytes())
        marker = b'air2lean-withheld-memory-' + secrets.token_hex(32).encode()
        scanner_source = SCANNER.replace('__MARKER_LENGTH__', str(len(marker))).replace(
            '__MARKER_DIGEST__', hashlib.sha256(marker).hexdigest())
        scanner = fixture.write('tests/boundary/scan.py', scanner_source.encode())
        fixture.write('withheld-marker.txt', marker)
        fixture.write('.github/workflows/ci.yml', b'''jobs:
  producer:
    runs-on: ubuntu-24.04-arm
    steps:
      - name: Produce actual transport data
        run: |
          mkdir -p "$RUNNER_TEMP/payload"
          printf transported > "$RUNNER_TEMP/payload/token"
      - name: Upload actual transport data
        uses: actions/upload-artifact@pin
        with:
          name: boundary-payload
          path: ${{ runner.temp }}/payload/token
          if-no-files-found: error
  consumer:
    needs: producer
    runs-on: ubuntu-24.04-arm
    steps:
      - name: Download actual producer data
        uses: actions/download-artifact@pin
        with:
          name: boundary-payload
          path: imported
      - name: Probe actual runner and PID 1 memory
        run: |
          test "$(cat imported/token)" = transported
          exec python3 -B tests/boundary/scan.py --out "$RUNNER_TEMP/proc-boundary.json"
''')
        declaration = {'schema': 'air2lean-ci-inputs/2', 'parts': {
            name: {'inputs': ['scripts/**', '.github/**', 'tests/boundary/**', 'lean-toolchain', 'lakefile.toml']}
            for name in ('producer', 'consumer')
        }}
        fixture.write('.github/ci-inputs.json', json.dumps(declaration).encode())
        fixture.commit()
        fixture.pinned = fixture.revision()
        fixture.capture()
        positive_inputs = fixture.root / 'positive-inputs'
        positive_inputs.mkdir()
        source = positive_inputs / 'source.tar'
        source.write_bytes((fixture.snapshot / 'source.tar').read_bytes())
        history = positive_inputs / 'history.bundle'
        fixture.git('bundle', 'create', str(history), 'HEAD')
        archive_specs = {}
        for name, path in (('source', source), ('history', history)):
            payload = path.read_bytes()
            self.assertLessEqual(len(payload), 1024 * 1024, 'boundary fixture outgrew its scanner bound')
            archive_specs[name] = {'length': len(payload), 'sha256': hashlib.sha256(payload).hexdigest(),
                                   'prefix_hex': payload[:16].hex()}
        results = fixture.root / 'boundary-results'
        self.addCleanup(self.remove_run_containers, results)
        self.wrapper(fixture, results)
        runs = list(results.glob('run.*'))
        self.assertEqual(len(runs), 1)
        artifacts = runs[0]
        reports = {name: json.loads((artifacts / name / 'row.json').read_text())
                   for name in ('producer', 'consumer')}
        for name, report in reports.items():
            self.assertTrue(report['success'], name)
            self.assertTrue(report['restriction']['qualified'], name)
            self.assertTrue(report['restriction']['files_withheld'], name)
        image = reports['consumer']['image_id']
        self.assertRegex(image, r'^sha256:[0-9a-f]{64}$')
        self.assertEqual(reports['producer']['image_id'], image)
        identifiers = [self.container_id(artifacts / 'containers' / (name + '.id'))
                       for name in ('producer', 'consumer')]
        self.assertEqual(len(set(identifiers)), 2, 'each job must use a fresh container')
        for identifier in identifiers:
            absent = self.docker('inspect', identifier, check=False)
            self.assertNotEqual(absent.returncode, 0)
            self.assertIn('no such', absent.stderr.lower())
            self.assertIn(identifier, absent.stderr)
        negative = json.loads((artifacts / 'consumer/proc-boundary.json').read_text())
        self.assertTrue(any('local-ci-steps.py' in argument for argument in negative['parent']['cmdline']), negative)
        for role in ('parent', 'pid1'):
            self.assertNotEqual(negative[role]['pid'], negative['self_pid'])
            self.assertGreater(negative[role]['bytes_read'], 0, negative)
            self.assertEqual(negative[role]['errors'], [], negative)
            self.assertFalse(negative[role]['found'], negative)
            self.assertFalse(negative[role]['compressed_found'], negative)
            self.assertFalse(negative[role]['budget_exhausted'], negative)
        self.assertFalse(any(negative['archives'].values()), negative)
        self.assertEqual(negative['git_objects']['returncode'], 0, negative)
        self.assertFalse(negative['git_objects']['found'], negative)
        self.assertEqual((artifacts / 'uploads/boundary-payload/token').read_text(), 'transported')

        # PID 1 retains the actual capture and Git bundle bytes in the old
        # self.source/self.history representations. It removes the mounted files
        # before the scanner starts, so each archive must be recovered from memory.
        cidfile = fixture.root / 'positive-container.id'
        self.addCleanup(self.remove_owned_container, cidfile)
        parent = ('import subprocess,sys; from pathlib import Path; '
                  'source=Path("/positive/source.tar"); history=Path("/positive/history.bundle"); '
                  'retained_source=source.read_bytes(); retained_history=history.read_bytes(); '
                  'source.unlink(); history.unlink(); '
                  'subprocess.run([sys.executable,"-B","/scanner.py","--positive",'
                  '"--archive-specs",sys.argv[1]],check=True)')
        self.docker('create', '--platform', 'linux/arm64', '--cidfile', str(cidfile),
                    '--mount', 'type=bind,src=' + str(scanner) + ',dst=/scanner.py,readonly',
                    '--mount', 'type=bind,src=' + str(positive_inputs) + ',dst=/positive',
                    '--entrypoint', 'python3', image, '-B', '-c', parent, json.dumps(archive_specs))
        identifier = self.container_id(cidfile)
        positive_run = self.docker('start', '--attach', identifier)
        self.assertEqual(self.docker('wait', identifier).stdout.strip(), '0')
        positive = json.loads(positive_run.stdout)
        for role in ('parent', 'pid1'):
            self.assertEqual(positive[role]['pid'], 1, positive)
            self.assertGreater(positive[role]['bytes_read'], 0, positive)
            self.assertEqual(positive[role]['errors'], [], positive)
            self.assertFalse(positive[role]['budget_exhausted'], positive)
            self.assertEqual(set(positive[role]['archives']), {'source', 'history'})
            for archive in positive[role]['archives'].values():
                self.assertTrue(archive['found'], positive)
                self.assertTrue(archive['marker_recovered'], positive)
        self.assertNotEqual(positive['self_pid'], 1)
        self.assertFalse(source.exists())
        self.assertFalse(history.exists())
        self.remove_owned_container(cidfile)
        absent = self.docker('inspect', identifier, check=False)
        self.assertNotEqual(absent.returncode, 0)
        self.assertIn('no such', absent.stderr.lower())
        self.assertIn(identifier, absent.stderr)
        cidfile.unlink()
        positive_evidence = positive | {
            role: {key: value for key, value in positive[role].items() if key != 'cmdline'}
            for role in ('parent', 'pid1')
        }
        print(json.dumps({'boundary_evidence': {
            'schema': 'air2lean-local-ci-process-boundary/1',
            'source': reports['consumer']['source'], 'image_id': image,
            'rows': reports,
            'containers': dict(zip(('producer', 'consumer'), identifiers)) | {'positive': identifier},
            'container_cleanup': {'producer': 'removed', 'consumer': 'removed', 'positive': 'removed'},
            'positive_exit_status': 0,
            'negative': negative, 'positive': positive_evidence,
            'archive_specs': {name: {'length': spec['length'], 'sha256': spec['sha256']}
                              for name, spec in archive_specs.items()},
        }}, sort_keys=True), flush=True)


if __name__ == '__main__':
    unittest.main()
