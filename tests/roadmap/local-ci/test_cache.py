#!/usr/bin/env python3
"""Cache and source-capture regressions; no toolchain builds or containers."""
import ast
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import runpy
import stat
import subprocess
import sys
import tarfile
import tomllib
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[3]
source=ast.parse((ROOT/'scripts/local-ci-steps.py').read_text())
functions=[node for node in source.body if isinstance(node,ast.FunctionDef) and node.name in ('open_dir','prune_stale_modules','prune_current_cache')]
namespace=dict(os=os,Path=Path,re=re,stat=stat,subprocess=subprocess,tomllib=tomllib)
exec(compile(ast.Module(body=functions,type_ignores=[]),'cache-helper','exec'),namespace)
prune=namespace['prune_stale_modules']

class Cache(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name).resolve()
        self.current={'Proofs/Sync/RwLock.lean','ZigLean/Basic.lean','tools/Assurance.lean'}
        self.owners={'Proofs','ZigLean','Air2Lean','tools/Assurance'}
        for path in self.current:
            target=self.root/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_text('-- tracked source\n')

    def file(self,path):
        target=self.root/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b'cached bytes');return target

    def prune(self):return prune(self.root,self.current,self.owners)

    def test_standalone_cross_branch_hash_is_removed(self):
        stale=self.file('.lake/build/lib/lean/Proofs/Sync/RwLockContract.olean.hash')
        current=self.file('.lake/build/lib/lean/Proofs/Sync/RwLock.olean.hash')
        self.assertEqual(self.prune(),[str(stale.relative_to(self.root))])
        self.assertFalse(stale.exists());self.assertEqual(current.read_bytes(),b'cached bytes')

    def test_entire_pinned_artifact_group_removed_current_group_preserved(self):
        facets={'lib/lean':('olean','olean.private','olean.server','ilean','ir','ir.sig'),
                'ir':('c','c.o.export','c.o.noexport','bc','bc.o','ltar','setup.json')}
        stale=[];current=[]
        for directory,extensions in facets.items():
            for extension in extensions:
                for sidecar in ('','.hash','.trace'):
                    stale.append(self.file(f'.lake/build/{directory}/Proofs/Sync/RwLockContract.{extension}{sidecar}'))
                    current.append(self.file(f'.lake/build/{directory}/Proofs/Sync/RwLock.{extension}{sidecar}'))
        stale.append(self.file('.lake/build/lib/lean/Proofs/Sync/RwLockContract.trace'))
        current.append(self.file('.lake/build/lib/lean/Proofs/Sync/RwLock.trace'))
        self.assertEqual(set(self.prune()),{str(p.relative_to(self.root)) for p in stale})
        self.assertTrue(all(not p.exists() for p in stale));self.assertTrue(all(p.read_bytes()==b'cached bytes' for p in current))

    def test_unknown_foreign_packages_toolchains_and_user_source_preserved(self):
        keep=[self.file(p) for p in ('.lake/build/lib/lean/Proofs/Sync/RwLockContract.olean.backup',
              '.lake/build/lib/lean/Lean/Foreign.olean','.lake/build/lib/lean/Dependency/Foreign.olean',
              '.lake/packages/pkg/.lake/build/lib/lean/Proofs/Stale.olean',
              'toolchains/lib/lean/Proofs/Stale.olean','Proofs/Sync/User.lean',
              '.lake/build/ir/Proofs/Sync/User.lean')]
        self.assertEqual(self.prune(),[])
        self.assertTrue(all(p.read_bytes()==b'cached bytes' for p in keep))

    def test_no_follow_for_build_root_or_owned_subdirectory(self):
        outside=self.root/'outside';outside.mkdir();sentinel=self.file('outside/Stale.olean.hash')
        lake=self.root/'.lake';lake.symlink_to(outside,target_is_directory=True)
        with self.assertRaises(OSError):self.prune()
        self.assertEqual(sentinel.read_bytes(),b'cached bytes');lake.unlink()
        owned=self.root/'.lake/build/lib/lean/Proofs';owned.parent.mkdir(parents=True);owned.symlink_to(outside,target_is_directory=True)
        with self.assertRaises(ValueError):self.prune()
        self.assertEqual(sentinel.read_bytes(),b'cached bytes')

    def test_stale_artifact_symlink_is_not_unlinked_or_followed(self):
        sentinel=self.file('outside/user-data');link=self.root/'.lake/build/lib/lean/Proofs/Sync/Stale.olean.hash'
        link.parent.mkdir(parents=True);link.symlink_to(sentinel)
        safe=self.file('.lake/build/lib/lean/Proofs/Sync/Other.olean.hash')
        with self.assertRaises(ValueError):self.prune()
        self.assertTrue(link.is_symlink());self.assertTrue(safe.exists());self.assertEqual(sentinel.read_bytes(),b'cached bytes')

    def test_hardlinked_artifacts_do_not_delete_shared_contents(self):
        source=self.file('Proofs/Sync/User.lean')
        for name in ('First','Second'):
            target=self.root/f'.lake/build/lib/lean/Proofs/Sync/{name}.olean'
            target.parent.mkdir(parents=True,exist_ok=True);os.link(source,target)
        self.assertEqual(len(self.prune()),2);self.assertEqual(source.read_bytes(),b'cached bytes')

    def test_missing_cache_and_explicit_module_root_are_conservative(self):
        self.assertEqual(self.prune(),[])
        stale=self.file('.lake/build/lib/lean/tools/Assurance.olean.hash')
        sibling=self.file('.lake/build/lib/lean/tools/User.olean.hash')
        self.current.remove('tools/Assurance.lean')
        self.assertEqual(self.prune(),[str(stale.relative_to(self.root))]);self.assertTrue(sibling.exists())
        with self.assertRaises(ValueError):prune(self.root,self.current,{'../unsafe'})

    def test_current_configuration_uses_tracked_git_names_and_declared_roots(self):
        (self.root/'lakefile.toml').write_text((ROOT/'lakefile.toml').read_text())
        (self.root/'lean-toolchain').write_text((ROOT/'lean-toolchain').read_text())
        target=self.file('.lake/build/lib/lean/Proofs/Sync/RwLockContract.olean.hash')
        current=self.file('.lake/build/lib/lean/Proofs/Sync/RwLock.olean.hash')
        fake=SimpleNamespace(stdout=('\0'.join(sorted(self.current))+'\0').encode())
        with patch.object(subprocess,'run',return_value=fake) as git,patch('builtins.print'):
            removed=namespace['prune_current_cache'](self.root)
        self.assertEqual(removed,[str(target.relative_to(self.root))]);self.assertTrue(current.exists())
        self.assertEqual(git.call_args.args[0],['git','-C',str(self.root),'ls-files','-z'])
        self.assertEqual(git.call_args.kwargs['timeout'],5)
        (self.root/'lean-toolchain').write_text('leanprover/lean4:vNEXT\n')
        with patch.object(subprocess,'run') as git,self.assertRaises(ValueError):namespace['prune_current_cache'](self.root)
        git.assert_not_called()

    def test_custom_layout_is_refused_before_pruning(self):
        (self.root/'lean-toolchain').write_text((ROOT/'lean-toolchain').read_text())
        (self.root/'lakefile.toml').write_text('name="test"\nbuildDir="user-data"\n')
        target=self.file('.lake/build/lib/lean/Proofs/Sync/Stale.olean')
        with patch.object(subprocess,'run') as git,self.assertRaises(ValueError):namespace['prune_current_cache'](self.root)
        git.assert_not_called();self.assertTrue(target.exists())

    def test_replaced_artifact_identity_blocks_deletion(self):
        target=self.file('.lake/build/lib/lean/Proofs/Sync/Stale.olean')
        real_stat=os.stat;count=0
        def changed(path,*args,**kwargs):
            nonlocal count
            if path=='Stale.olean':
                count+=1
                if count==2:target.write_bytes(b'new current artifact')
            return real_stat(path,*args,**kwargs)
        with patch.object(os,'stat',side_effect=changed),self.assertRaises(ValueError):self.prune()
        self.assertEqual(target.read_bytes(),b'new current artifact')

class Capture(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='local-ci-capture-test-')
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name).resolve()
        self.repo=self.root/'repo';self.repo.mkdir()
        self.snapshot=self.root/'snapshot';self.snapshot.mkdir()
        self.artifacts=self.root/'artifacts';self.artifacts.mkdir()
        self.previous=Path.cwd();os.chdir(self.repo)
        self.addCleanup(os.chdir,self.previous)
        environment={key:value for key,value in os.environ.items() if not key.startswith('GIT_')}
        environment.update(GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL=os.devnull)
        clean_environment=patch.dict(os.environ,environment,clear=True)
        clean_environment.start();self.addCleanup(clean_environment.stop)
        self.git('init','-q','--object-format=sha1')
        self.configure_git()
        self.write('gate.txt',b'original gate\n')
        self.commit()
        self.pinned=self.revision()

    def git(self,*args):
        return subprocess.run(['git','-C',str(self.repo),*args],check=True,
                              stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout

    def configure_git(self):
        for key,value in (('user.name','capture test'),('user.email','capture@example.invalid'),
                          ('core.filemode','true'),('core.symlinks','true'),('core.autocrlf','false')):
            self.git('config',key,value)

    def write(self,name,content):
        path=self.repo/name;path.parent.mkdir(parents=True,exist_ok=True)
        path.write_bytes(content)
        return path

    def commit(self):
        self.git('add','-f','--','.')
        self.git('commit','-qm','capture fixture')

    def revision(self):
        return self.git('rev-parse','HEAD').decode().strip()

    def capture(self,error=None,mode='full',version='0.17.0'):
        script=ROOT/'scripts/local-ci-steps.py'
        argv=[str(script),'--snapshot',str(self.snapshot),str(self.artifacts),mode,version]
        with patch.object(sys,'argv',argv),self.assertRaises(SystemExit) as stopped:
            runpy.run_path(str(script),run_name='__main__')
        if error is not None:
            self.assertNotEqual(stopped.exception.code,0)
            self.assertRegex(str(stopped.exception.code),error)
            for directory in (self.snapshot,self.artifacts):
                self.assertFalse((directory/'source-revision').exists())
            return
        self.assertEqual(stopped.exception.code,0)
        stamp=(self.artifacts/'source-revision').read_text()
        self.assertEqual((self.snapshot/'source-revision').read_text(),stamp)
        values=dict(line.split('=',1) for line in stamp.splitlines())
        self.assertEqual(values['mode'],'full');self.assertEqual(values['version'],'0.17.0')
        self.assertEqual(values['snapshot_sha256'],hashlib.sha256((self.snapshot/'source.tar').read_bytes()).hexdigest())
        return values

    def fail_capture(self,pattern,**labels):
        for directory in (self.snapshot,self.artifacts):
            (directory/'source-revision').write_text('revision=stale\ntracked_clean=yes\n')
        self.capture(error=pattern,**labels)

    def assert_dirty_snapshot(self,stamp):
        self.assertEqual(stamp['revision'],self.pinned)
        self.assertEqual(stamp['tracked_clean'],'no')

    def test_clean_capture_preserves_raw_bytes_modes_links_names_and_export_attributes(self):
        regular={'empty':b'','binary.dat':b'\0\xff\r\nraw\0bytes',
                 'space name':b'spaces','line\nname':b'newlines','tab\tname':b'tabs',
                  '-leading':b'option-looking name','caf\u00e9':b'non-ASCII path','120000':b'literal link target',
                 'directory/member':b'directory source','exported.txt':b'export ignored but tracked',
                 'substituted.txt':b'$Format:%H$\n',
                 '.gitattributes':b'exported.txt export-ignore\nsubstituted.txt export-subst\n'}
        for name,content in regular.items():self.write(name,content)
        executable=self.write('executable.sh',b'#!/bin/sh\nexit 0\n');executable.chmod(0o755)
        (self.repo/'symbolic').symlink_to('120000')
        (self.repo/'directory-link').symlink_to('directory',target_is_directory=True)
        excluded=('.lake/cache','nested/.lake/cache','.aws/private','.codex/private','.agents/private',
                  'host-zig/bin/zig','zig-air-0.17.0/bin/zig')
        for name in excluded:self.write(name,b'excluded tracked bytes')
        self.commit();self.pinned=self.revision()
        self.write('directory/untracked',b'must not follow directory symlink')
        stamp=self.capture()
        self.assertEqual(stamp['revision'],self.pinned);self.assertEqual(stamp['tracked_clean'],'yes')
        expected=set(regular)|{'gate.txt','executable.sh','symbolic','directory-link'}
        inventory=(self.snapshot/'files').read_bytes().split(b'\0')
        self.assertEqual(inventory[-1],b'')
        self.assertEqual({os.fsdecode(name) for name in inventory[:-1]},expected)
        with tarfile.open(self.snapshot/'source.tar') as archive:
            self.assertEqual(set(archive.getnames()),expected)
            for name,content in regular.items():self.assertEqual(archive.extractfile(name).read(),content)
            self.assertTrue(archive.getmember('executable.sh').mode&stat.S_IXUSR)
            self.assertTrue(archive.getmember('symbolic').issym())
            self.assertEqual(archive.getmember('symbolic').linkname,'120000')
            self.assertTrue(archive.getmember('directory-link').issym())
            self.assertEqual(archive.getmember('directory-link').linkname,'directory')

    def test_restored_working_bytes_do_not_qualify_dirty_archived_bytes(self):
        gate=self.repo/'gate.txt';original=gate.read_bytes();actual_add=tarfile.TarFile.add
        def transient_edit(archive,name,*args,**kwargs):
            if name!='gate.txt':return actual_add(archive,name,*args,**kwargs)
            gate.write_bytes(b'dirty archived gate\n')
            try:return actual_add(archive,name,*args,**kwargs)
            finally:gate.write_bytes(original)
        with patch.object(tarfile.TarFile,'add',transient_edit):stamp=self.capture()
        self.assert_dirty_snapshot(stamp)
        self.assertEqual(self.git('status','--porcelain','--untracked-files=no'),b'')
        with tarfile.open(self.snapshot/'source.tar') as archive:
            self.assertEqual(archive.extractfile('gate.txt').read(),b'dirty archived gate\n')
        spec=importlib.util.spec_from_file_location('capture_release_record',ROOT/'scripts/release-record.py')
        release=importlib.util.module_from_spec(spec);spec.loader.exec_module(release)
        (self.artifacts/'exit-status').write_text('0\n');(self.artifacts/'container.log').write_bytes(b'')
        with self.assertRaisesRegex(release.ReleaseError,'snapshot had tracked changes'):
            release.local_ci_evidence(self.artifacts,self.pinned,{})

    def test_restored_executable_mode_does_not_qualify_archived_mode(self):
        gate=self.repo/'gate.txt';actual_add=tarfile.TarFile.add
        def transient_mode(archive,name,*args,**kwargs):
            if name!='gate.txt':return actual_add(archive,name,*args,**kwargs)
            original=stat.S_IMODE(gate.stat().st_mode);gate.chmod(0o755)
            try:return actual_add(archive,name,*args,**kwargs)
            finally:gate.chmod(original)
        with patch.object(tarfile.TarFile,'add',transient_mode):stamp=self.capture()
        self.assert_dirty_snapshot(stamp)
        self.assertEqual(self.git('status','--porcelain','--untracked-files=no'),b'')
        with tarfile.open(self.snapshot/'source.tar') as archive:
            self.assertTrue(archive.getmember('gate.txt').mode&stat.S_IXUSR)

    def test_restored_symlink_target_or_type_does_not_qualify_archive(self):
        link=self.repo/'link';link.symlink_to('gate.txt');self.commit();self.pinned=self.revision()
        actual_add=tarfile.TarFile.add
        for replacement in ('target','type'):
            with self.subTest(replacement=replacement):
                def transient_link(archive,name,*args,**kwargs):
                    if name!='link':return actual_add(archive,name,*args,**kwargs)
                    link.unlink()
                    if replacement=='target':link.symlink_to('different-target')
                    else:link.write_bytes(b'gate.txt')
                    try:return actual_add(archive,name,*args,**kwargs)
                    finally:link.unlink();link.symlink_to('gate.txt')
                with patch.object(tarfile.TarFile,'add',transient_link):stamp=self.capture()
                self.assert_dirty_snapshot(stamp)
                self.assertEqual(self.git('status','--porcelain','--untracked-files=no'),b'')

    def test_head_movement_keeps_pinned_revision_and_marks_snapshot_dirty(self):
        actual_add=tarfile.TarFile.add
        def move_head(archive,name,*args,**kwargs):
            result=actual_add(archive,name,*args,**kwargs)
            if name=='gate.txt':self.git('commit','--allow-empty','-qm','advance during capture')
            return result
        with patch.object(tarfile.TarFile,'add',move_head):stamp=self.capture()
        self.assertNotEqual(self.revision(),self.pinned)
        self.assert_dirty_snapshot(stamp)
        self.assertEqual(self.git('status','--porcelain','--untracked-files=no'),b'')

    def test_staged_additions_deletions_and_missing_working_files_stay_dirty(self):
        for change in ('staged addition','staged deletion','unstaged missing'):
            with self.subTest(change=change):
                self.git('reset','--hard',self.pinned)
                if change=='staged addition':
                    self.write('added.txt',b'new indexed file');self.git('add','--','added.txt')
                elif change=='staged deletion':self.git('rm','--','gate.txt')
                else:(self.repo/'gate.txt').unlink()
                self.assert_dirty_snapshot(self.capture())

    def test_unavailable_git_tree_comparison_removes_stale_stamps_and_fails_closed(self):
        actual_run=subprocess.run
        def unavailable_tree(command,*args,**kwargs):
            if command[0]=='git' and 'ls-tree' in command:
                return subprocess.CompletedProcess(command,128,stdout=b'',stderr=b'injected tree read failure')
            return actual_run(command,*args,**kwargs)
        with patch.object(subprocess,'run',unavailable_tree):
            self.fail_capture('cannot establish snapshot identity.*injected tree read failure')

    def test_multiline_stamp_labels_fail_without_preserving_a_stale_stamp(self):
        for separator in ('\n','\r','\v','\f','\x1c','\x1d','\x1e','\x85','\u2028','\u2029'):
            for key,prefix in (('mode','full'),('version','0.17.0')):
                with self.subTest(separator=repr(separator),key=key):
                    self.fail_capture('source stamp labels must be single lines',
                                      **{key:prefix+separator+'tracked_clean=yes'})

    def seal(self,error=None):
        script=ROOT/'scripts/local-ci-steps.py'
        bootstrap=self.root/'local-ci.sh'
        argv=[str(script),'--seal-snapshot',str(self.snapshot),str(bootstrap)]
        with patch.object(sys,'argv',argv),self.assertRaises(SystemExit) as stopped:
            runpy.run_path(str(script),run_name='__main__')
        if error is not None:
            self.assertNotEqual(stopped.exception.code,0)
            self.assertRegex(str(stopped.exception.code),error)
        else:self.assertEqual(stopped.exception.code,0)

    def test_workflow_cannot_read_archive_or_stale_source_copies_after_sealing(self):
        self.capture()
        (self.snapshot/'Dockerfile').write_bytes(b'temporary image recipe')
        (self.snapshot/'bootstrap.sh').write_bytes(b'captured temporary bootstrap')
        (self.root/'local-ci.sh').write_bytes(b'temporary bootstrap')
        for path in ('.lake/check-tree/old/withheld.txt','tests/diff/.lake/check-tree/old/withheld.txt'):
            self.write(path,b'previous unrestricted source')
        facet=self.write('.lake/build/lib/lean/Current.olean',b'keep incremental facets')
        # The actual protected step can extract the otherwise-withheld bytes before sealing.
        command=['tar','-xOf',str(self.snapshot/'source.tar'),'gate.txt']
        self.assertEqual(subprocess.check_output(command),b'original gate\n')
        self.seal()
        step=subprocess.run(['bash','-e','-c',
                             'if tar -xOf "$1" gate.txt > "$2" 2>/dev/null; then exit 1; fi',
                             'workflow-step',str(self.snapshot/'source.tar'),str(self.root/'read-result')])
        self.assertEqual(step.returncode,0)
        for path in (self.snapshot/'source.tar',self.snapshot/'Dockerfile',self.snapshot/'files',self.snapshot/'bootstrap.sh',
                     self.root/'local-ci.sh',self.repo/'.lake/check-tree',self.repo/'tests/diff/.lake/check-tree'):
            self.assertFalse(os.path.lexists(path),str(path))
        self.assertEqual(facet.read_bytes(),b'keep incremental facets')

    def test_check_tree_symlink_is_unlinked_without_following_it(self):
        external=self.root/'outside';external.mkdir();(external/'keep').write_bytes(b'not a cache copy')
        (self.repo/'.lake').mkdir()
        (self.repo/'.lake/check-tree').symlink_to(external,target_is_directory=True)
        self.seal()
        self.assertFalse(os.path.lexists(self.repo/'.lake/check-tree'))
        self.assertEqual((external/'keep').read_bytes(),b'not a cache copy')

    def test_check_tree_symlink_parent_fails_closed_without_deleting_external_data(self):
        external=self.root/'outside';(external/'check-tree').mkdir(parents=True)
        (external/'check-tree/keep').write_bytes(b'not a cache copy')
        (self.repo/'.lake').symlink_to(external,target_is_directory=True)
        self.seal(error='local-ci isolation:')
        self.assertEqual((external/'check-tree/keep').read_bytes(),b'not a cache copy')

    def test_parent_replacement_cannot_redirect_check_tree_cleanup(self):
        self.write('.lake/check-tree/keep',b'owned old source copy')
        external=self.root/'outside';(external/'check-tree').mkdir(parents=True)
        canary=external/'check-tree/keep';canary.write_bytes(b'external user data')
        actual_open=os.open;swapped=False
        def swap_after_open(path,*args,**kwargs):
            nonlocal swapped
            descriptor=actual_open(path,*args,**kwargs)
            if path=='.lake' and not swapped:
                swapped=True
                (self.repo/'.lake').rename(self.repo/'.lake-original')
                (self.repo/'.lake').symlink_to(external,target_is_directory=True)
            return descriptor
        with patch.object(os,'open',swap_after_open):self.seal()
        self.assertTrue(swapped)
        self.assertEqual(canary.read_bytes(),b'external user data')
        self.assertFalse((self.repo/'.lake-original/check-tree').exists())

    def part_fixture(self,duplicate=False):
        row='''          - zig: "0.17.0"
            part: "isolation"
            examples: ""
            full: false
            mutate: false
'''
        workflow='''name: CI
jobs:
  test:
    runs-on: ubuntu-24.04
    strategy:
      matrix:
        include:
'''+row+(row if duplicate else '')+'''    steps:
      - name: Original Git source must be unavailable
        if: ${{ matrix.part == 'isolation' && runner.os == 'Linux' }}
        env:
          SHARED_CONTEXT: ${{ format('{0}/{1}', github.workspace, matrix.part) }}
        run: |
          [ "$SHARED_CONTEXT" = /work/isolation ]
          if tar -xOf "$AIR2LEAN_TEST_ARCHIVE" withheld.txt 2>/dev/null; then
            exit 1
          fi
          if git show "$AIR2LEAN_TEST_HEAD:withheld.txt" > "$AIR2LEAN_TEST_RECOVERY" 2>/dev/null; then
            exit 1
          fi
          python3 scripts/ci-reuse.py check-restricted
'''
        self.write('.github/workflows/ci.yml',workflow.encode())
        declaration={'schema':'air2lean-ci-inputs/2','parts':{
            'test/0.17.0/isolation':{'inputs':['gate.txt','scripts/**','lean-toolchain','lakefile.toml']}}}
        self.write('.github/ci-inputs.json',json.dumps(declaration).encode())
        for name in ('ci-reuse.py','release-record.py','generated.py','target-matrix.py','cas.py'):
            self.write('scripts/'+name,(ROOT/'scripts'/name).read_bytes())
        self.write('lean-toolchain',(ROOT/'lean-toolchain').read_bytes())
        self.write('lakefile.toml',b'name = "local_ci_isolation"\n')
        self.write('withheld.txt',b'unique committed source canary\n')
        self.commit();self.pinned=self.revision()
        spec=importlib.util.spec_from_file_location('part_release_parser',ROOT/'scripts/release-record.py')
        release=importlib.util.module_from_spec(spec);spec.loader.exec_module(release)
        return release.parse_workflow_yaml(workflow)

    def run_part_interpreter(self,workflow):
        from contextlib import nullcontext
        import signal

        actual_popen=subprocess.Popen;actual_mkdir=Path.mkdir;executed=[]
        def popen(command,*args,**kwargs):
            executed.append(command)
            if command==['bash','scripts/local-ci.sh','--prepare','0.17.0']:
                return nullcontext(SimpleNamespace(wait=lambda:0))
            # The host test has no container cache lock on FD9. All Git and protected
            # shell commands still execute normally in their own process groups.
            if 'pass_fds' in kwargs:kwargs['pass_fds']=()
            return actual_popen(command,*args,**kwargs)
        def mkdir(path,*args,**kwargs):
            if str(path)=='/artifacts/row-0-0.17.0':
                path=self.artifacts/'part-row'
            return actual_mkdir(path,*args,**kwargs)
        handlers={signum:signal.getsignal(signum) for signum in (signal.SIGTERM,signal.SIGINT)}
        script=ROOT/'scripts/local-ci-steps.py'
        recovery=self.root/'recovered-source'
        try:
            with patch.object(sys,'argv',[str(script),'part','test/0.17.0/isolation']),\
                 patch.dict(sys.modules,{'yaml':SimpleNamespace(safe_load=lambda text:workflow)}),\
                 patch.object(subprocess,'Popen',popen),patch.object(Path,'mkdir',mkdir),\
                 patch.dict(os.environ,ELAN_HOME=str(self.root/'elan'),AIR2LEAN_TEST_HEAD=self.pinned,
                             AIR2LEAN_TEST_ARCHIVE=str(self.snapshot/'source.tar'),
                            AIR2LEAN_TEST_RECOVERY=str(recovery)):
                runpy.run_path(str(script),run_name='__main__')
        finally:
            for signum,handler in handlers.items():signal.signal(signum,handler)
        return executed,recovery

    def test_actual_part_interpreter_seals_original_git_objects_before_protected_step(self):
        workflow=self.part_fixture()
        # This is the precise recovery route the actual protected step attempts later.
        self.assertEqual(self.git('show',self.pinned+':withheld.txt'),b'unique committed source canary\n')
        self.capture()
        with tarfile.open(self.snapshot/'source.tar') as archive:
            self.assertEqual(archive.extractfile('withheld.txt').read(),b'unique committed source canary\n')
        self.seal()
        executed,recovery=self.run_part_interpreter(workflow)
        self.assertTrue(recovery.exists());self.assertEqual(recovery.read_bytes(),b'')
        self.assertIn(['python3','scripts/ci-reuse.py','restrict','--part','test/0.17.0/isolation','--seal'],executed)
        with self.assertRaises(subprocess.CalledProcessError):
            self.git('show',self.pinned+':withheld.txt')

    def test_duplicate_part_rows_fail_before_preparation_or_workflow_execution(self):
        workflow=self.part_fixture(duplicate=True)
        with patch.object(subprocess,'Popen') as started,\
             self.assertRaisesRegex(ValueError,'must match exactly one matrix row'):
            self.run_part_interpreter(workflow)
        started.assert_not_called()

    def test_actual_part_rejects_unknown_shared_condition(self):
        workflow=self.part_fixture()
        workflow['jobs']['test']['steps'][0]['if']='${{ unsupported.context }}'
        with self.assertRaisesRegex(Exception,'unsupported term'):
            self.run_part_interpreter(workflow)

    def test_actual_wrapper_uses_archived_recipe_and_cache_inputs_after_live_edits(self):
        self.part_fixture()
        for name in ('local-ci.sh','local-ci-steps.py','zig-default.sh'):
            self.write('scripts/'+name,(ROOT/'scripts'/name).read_bytes())
        os.link(self.repo/'scripts/local-ci.sh',self.repo/'.bootstrap-source')
        self.write('Dockerfile.local-ci',b'FROM archived-image\n')
        root_toolchain=b'archived root toolchain\n';root_manifest=b'{"archived":"root"}\n'
        diff_toolchain=root_toolchain;diff_manifest=b'{"archived":"diff"}\n'
        for name,content in (('lean-toolchain',root_toolchain),('lake-manifest.json',root_manifest),
                             ('tests/diff/lean-toolchain',diff_toolchain),('tests/diff/lake-manifest.json',diff_manifest)):
            self.write(name,content)
        (self.repo/'tests/diff/lean-toolchain').unlink()
        os.link(self.repo/'lean-toolchain',self.repo/'tests/diff/lean-toolchain')
        os.link(self.repo/'Dockerfile.local-ci',self.repo/'.image-recipe')
        self.commit();self.pinned=self.revision()
        binary=self.root/'bin';binary.mkdir();docker=binary/'docker'
        python=binary/'python3'
        python.write_text('#!'+sys.executable+'\n'+'''
import runpy,subprocess,sys
from pathlib import Path
from unittest.mock import patch
if '--snapshot-runner' not in sys.argv:
    raise SystemExit(subprocess.run([sys.executable,*sys.argv[1:]]).returncode)
arguments=sys.argv[1:]
if arguments[0]=='-B':
    arguments=arguments[1:];sys.dont_write_bytecode=True
snapshot=Path(arguments[2]);actual_write=Path.write_text
def after_stamp(path,*args,**kwargs):
    result=actual_write(path,*args,**kwargs)
    if path==snapshot/'source-revision':
        for name in ('Dockerfile.local-ci','lean-toolchain','lake-manifest.json',
                     'tests/diff/lean-toolchain','tests/diff/lake-manifest.json'):
            Path(name).write_bytes(b'changed after capture\\n')
    return result
sys.argv=arguments
with patch.object(Path,'write_text',after_stamp):
    runpy.run_path(arguments[0],run_name='__main__')
''')
        python.chmod(0o755)
        docker.write_text('''#!/usr/bin/env python3
import json,os,sys
from pathlib import Path
command=sys.argv[1]
if command=='info':
    print('amd64')
elif command=='build':
    Path(os.environ['AIR2LEAN_TEST_IMAGE_RECIPE']).write_bytes(sys.stdin.buffer.read())
elif command=='create':
    mount=next(arg for arg in sys.argv if arg.startswith('type=bind,src='))
    snapshot=Path(mount.split('src=',1)[1].split(',dst=',1)[0])
    Path(os.environ['AIR2LEAN_TEST_BOOTSTRAP']).write_bytes((snapshot/'bootstrap.sh').read_bytes())
    Path(os.environ['AIR2LEAN_TEST_CREATE_ARGS']).write_text(json.dumps(sys.argv[2:]))
    raise SystemExit(73)  # Stop before any real container or workflow launch.
else:
    raise SystemExit('unexpected Docker command: '+command)
''')
        docker.chmod(0o755)
        recipe=self.root/'image-recipe';arguments=self.root/'create-args';bootstrap=self.root/'bootstrap'
        environment=dict(os.environ,PATH=str(binary)+os.pathsep+os.environ['PATH'],
                         AIR2LEAN_LOCAL_RESULTS=str(self.artifacts),
                         AIR2LEAN_TEST_IMAGE_RECIPE=str(recipe),AIR2LEAN_TEST_CREATE_ARGS=str(arguments),
                         AIR2LEAN_TEST_BOOTSTRAP=str(bootstrap))
        result=subprocess.run(['bash',str(self.repo/'scripts/local-ci.sh'),'full','0.17.0'],
                              env=environment,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        self.assertEqual(result.returncode,73,result.stderr.decode(errors='replace'))
        self.assertEqual(recipe.read_bytes(),b'FROM archived-image\n')
        self.assertEqual(bootstrap.read_bytes(),(ROOT/'scripts/local-ci.sh').read_bytes())
        self.assertEqual((self.repo/'Dockerfile.local-ci').read_bytes(),b'changed after capture\n')
        results=next(self.artifacts.glob('run.*/source-revision')).read_text()
        self.assertIn('tracked_clean=yes\n',results)
        values=json.loads(arguments.read_text())
        self.assertIn('exec bash /snapshot/bootstrap.sh --inside "$@"',values)
        root_key=hashlib.sha256(root_toolchain+root_manifest).hexdigest()[:16]
        diff_key=hashlib.sha256(diff_toolchain+diff_manifest).hexdigest()[:16]
        self.assertTrue(any('lake-'+root_key+',dst=/work/.lake' in value for value in values))
        self.assertTrue(any('diff-'+diff_key+',dst=/work/tests/diff/.lake' in value for value in values))
        for missing in ('lean-toolchain','tests/diff/lean-toolchain'):
            with self.subTest(missing=missing):
                self.git('reset','--hard',self.pinned)
                (self.repo/missing).unlink();arguments.unlink(missing_ok=True)
                result=subprocess.run(['bash',str(self.repo/'scripts/local-ci.sh'),'full','0.17.0'],
                                      env=environment,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
                self.assertNotEqual(result.returncode,0)
                self.assertNotEqual(result.returncode,73,result.stderr.decode(errors='replace'))
                self.assertFalse(arguments.exists())
                self.assertIn(missing.encode(),result.stderr)
        for symbolic in ('Dockerfile.local-ci','lean-toolchain'):
            with self.subTest(symbolic=symbolic):
                self.git('reset','--hard',self.pinned)
                (self.repo/symbolic).unlink();(self.repo/symbolic).symlink_to('gate.txt')
                arguments.unlink(missing_ok=True);recipe.unlink(missing_ok=True)
                result=subprocess.run(['bash',str(self.repo/'scripts/local-ci.sh'),'full','0.17.0'],
                                      env=environment,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
                self.assertNotEqual(result.returncode,0)
                self.assertFalse(arguments.exists());self.assertFalse(recipe.exists())
                self.assertIn(b'unsupported snapshot regular member',result.stderr)

    def test_configuration_rejects_archive_changes_after_validated_capture(self):
        self.capture()
        with (self.snapshot/'source.tar').open('ab') as archive:archive.write(b'changed archive bytes')
        script=ROOT/'scripts/local-ci-steps.py'
        with patch.object(sys,'argv',[str(script),'--snapshot-config',str(self.snapshot)]),\
             self.assertRaisesRegex(SystemExit,'snapshot archive changed after capture'):
            runpy.run_path(str(script),run_name='__main__')
        self.assertFalse((self.snapshot/'Dockerfile').exists())

    def test_invalid_archive_inventory_and_member_types_fail_without_stamp(self):
        actual_add=tarfile.TarFile.add
        cases=(('duplicate','duplicate snapshot member'),('unexpected','unexpected snapshot member'),
               ('../escape','unsafe snapshot member'),('/absolute','unsafe snapshot member'),
               ('dir//entry','unsafe snapshot member'),('./gate.txt','unsafe snapshot member'),
               ('missing','missing snapshot members'),('unsupported','unsupported snapshot member type'))
        for mutation,diagnostic in cases:
            with self.subTest(mutation=mutation):
                def inject(archive,name,*args,**kwargs):
                    if name!='gate.txt':return actual_add(archive,name,*args,**kwargs)
                    if mutation=='missing':return
                    if mutation=='unsupported':
                        member=tarfile.TarInfo('gate.txt');member.type=tarfile.FIFOTYPE
                        return archive.addfile(member)
                    actual_add(archive,name,*args,**kwargs)
                    member=tarfile.TarInfo('gate.txt' if mutation=='duplicate' else
                                           'unexpected.txt' if mutation=='unexpected' else mutation)
                    member.size=1;archive.addfile(member,io.BytesIO(b'x'))
                with patch.object(tarfile.TarFile,'add',inject):self.fail_capture(diagnostic)

    def test_valid_hardlinks_preserve_git_identity(self):
        original=self.write('a.txt',b'hardlinked source')
        os.link(original,self.repo/'b.txt');self.commit();self.pinned=self.revision()
        stamp=self.capture()
        self.assertEqual(stamp['tracked_clean'],'yes');self.assertEqual(stamp['revision'],self.pinned)
        with tarfile.open(self.snapshot/'source.tar') as archive:
            self.assertTrue(archive.getmember('b.txt').islnk())
            self.assertEqual(archive.extractfile('b.txt').read(),b'hardlinked source')

    def test_unresolved_hardlinks_and_executable_mode_aliases_fail_closed(self):
        self.write('a.txt',b'same bytes');self.write('b.txt',b'same bytes');self.commit()
        actual_add=tarfile.TarFile.add
        for target,mode in (('not-in-inventory',0o644),('a.txt',0o755)):
            with self.subTest(target=target,mode=mode):
                def inject(archive,name,*args,**kwargs):
                    if name!='b.txt':return actual_add(archive,name,*args,**kwargs)
                    member=tarfile.TarInfo('b.txt');member.type=tarfile.LNKTYPE
                    member.linkname=target;member.mode=mode
                    archive.addfile(member)
                with patch.object(tarfile.TarFile,'add',inject):
                    self.fail_capture('unsupported snapshot regular member')

    def test_sha256_repository_uses_its_actual_git_blob_algorithm(self):
        self.repo=self.root/'sha256';self.repo.mkdir();os.chdir(self.repo)
        result=subprocess.run(['git','init','-q','--object-format=sha256'],
                              stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        if result.returncode:self.skipTest('installed Git does not support SHA-256 repositories')
        self.configure_git();self.write('gate.txt',b'raw SHA-256 source\0\xff')
        self.commit();self.pinned=self.revision()
        self.assertEqual(len(self.pinned),64)
        stamp=self.capture()
        self.assertEqual(stamp['revision'],self.pinned);self.assertEqual(stamp['tracked_clean'],'yes')


if __name__=='__main__':unittest.main()
