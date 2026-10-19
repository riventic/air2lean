#!/usr/bin/env python3
"""Cache and workflow-adapter regressions; no toolchain builds or containers."""
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from types import SimpleNamespace
import tempfile
import io
import tarfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[3]
spec=importlib.util.spec_from_file_location('local_ci_steps',ROOT/'scripts/local-ci-steps.py')
runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
prune=runner.prune_stale_modules

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
            removed=runner.prune_current_cache(self.root)
        self.assertEqual(removed,[str(target.relative_to(self.root))]);self.assertTrue(current.exists())
        self.assertEqual(git.call_args.args[0],['git','-C',str(self.root),'ls-files','-z'])
        self.assertEqual(git.call_args.kwargs['timeout'],5)
        (self.root/'lean-toolchain').write_text('leanprover/lean4:vNEXT\n')
        with patch.object(subprocess,'run') as git,self.assertRaises(ValueError):runner.prune_current_cache(self.root)
        git.assert_not_called()

    def test_custom_layout_is_refused_before_pruning(self):
        (self.root/'lean-toolchain').write_text((ROOT/'lean-toolchain').read_text())
        (self.root/'lakefile.toml').write_text('name="test"\nbuildDir="user-data"\n')
        target=self.file('.lake/build/lib/lean/Proofs/Sync/Stale.olean')
        with patch.object(subprocess,'run') as git,self.assertRaises(ValueError):runner.prune_current_cache(self.root)
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

class Workflow(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name).resolve()
        self.artifacts=self.root/'artifacts';self.artifacts.mkdir()
        (self.artifacts/'source-revision').write_text('revision=test\ntracked_clean=yes\n')
        self.snapshot=self.root/'snapshot';self.snapshot.mkdir()
        (self.snapshot/'source.tar').write_bytes(b'tested snapshot')
        (self.root/'.github').mkdir()
        (self.root/'.github/workflows').mkdir()
        (self.root/'.github/workflows/ci.yml').write_text('tested workflow\n')
        (self.root/'scripts').mkdir()
        (self.root/'scripts/ci-reuse.py').write_text('raise SystemExit(0)\n')
        self.previous=Path.cwd();os.chdir(self.root);self.addCleanup(os.chdir,self.previous)
        self.runner_name='macos-14' if sys.platform=='darwin' else {'x86_64':'ubuntu-24.04','aarch64':'ubuntu-24.04-arm'}[os.uname().machine]

    def workflow(self,steps,name='sample',**fields):
        (self.snapshot/'source.tar').write_bytes(b'tested snapshot')
        job={'runs-on':self.runner_name,'steps':steps}|fields
        (self.root/'.github/ci-inputs.json').write_text(json.dumps({'schema':'air2lean-ci-inputs/2','parts':{name:{'reuse':False}}}))
        return {'jobs':{name:job}}

    def run_row(self,workflow,name='sample'):
        run=runner.WorkflowRun(workflow,self.artifacts,self.snapshot)
        run.run_row(name,name,{})
        return json.loads((self.artifacts/name/'row.json').read_text())

    def test_native_workflow_commands_and_github_command_files_execute(self):
        workflow=self.workflow([
            {'name':'cache','id':'restore','uses':'actions/cache/restore@pin','with':{'path':'.lake','key':'test'}},
            {'name':'installer','if':"steps.restore.outputs.cache-hit != 'true'",'id':'install',
             'run':'echo "ANSWER=42" >> "$GITHUB_ENV"\necho "value=ok" >> "$GITHUB_OUTPUT"\necho "$RUNNER_TEMP/bin" >> "$GITHUB_PATH"'},
            {'name':'consumer','if':"${{ success() && steps.install.outputs.value == 'ok' }}",
             'run':'test "$ANSWER" = 42\ntest "${PATH%%:*}" = "$RUNNER_TEMP/bin"\nprintf executed > "$RUNNER_TEMP/result"'}])
        report=self.run_row(workflow)
        self.assertTrue(report['success'])
        self.assertEqual((self.artifacts/'sample/result').read_text(),'executed')
        self.assertTrue(all(step['status']=='passed' for step in report['steps']))
        self.assertEqual(report['source'],'revision=test\ntracked_clean=yes\n')
        self.assertEqual(len(report['snapshot_sha256']),64)

    def test_unsupported_action_fails_closed_and_records_failure(self):
        workflow=self.workflow([{'name':'unqualified action','uses':'third-party/do-anything@pin'}])
        with self.assertRaisesRegex(ValueError,'unsupported CI action'):
            self.run_row(workflow)
        report=json.loads((self.artifacts/'sample/row.json').read_text())
        self.assertFalse(report['success'])

    def test_unsupported_step_field_fails_before_running_command(self):
        workflow=self.workflow([{'name':'foreign shell','shell':'powershell','run':'touch unsafe'}])
        with self.assertRaisesRegex(ValueError,'unsupported CI step fields'):
            self.run_row(workflow)
        self.assertFalse((self.root/'unsafe').exists())

    def test_failed_continue_on_error_is_not_a_green_local_gate(self):
        workflow=self.workflow([{'name':'bad producer','continue-on-error':True,'run':'exit 7'}])
        with self.assertRaisesRegex(ValueError,'workflow steps failed'):self.run_row(workflow)
        report=json.loads((self.artifacts/'sample/row.json').read_text())
        self.assertFalse(report['success']);self.assertEqual(report['steps'][0]['status'],'failed')

    def test_missing_artifact_fails_with_exact_producer_reason(self):
        workflow=self.workflow([{'name':'download','uses':'actions/download-artifact@pin',
                                 'with':{'name':'not-produced','path':'download'}}])
        with self.assertRaisesRegex(ValueError,"not-produced.*no successful local producer"):
            self.run_row(workflow)

    def test_support_artifact_round_trip_uses_actual_upload(self):
        workflow=self.workflow([])
        run=runner.WorkflowRun(workflow,self.artifacts,self.snapshot)
        source=self.root/'packed';source.mkdir();(source/'build.tar').write_bytes(b'produced by workflow')
        context={}
        run.action({'name':'upload','uses':'actions/upload-artifact@pin',
                    'with':{'name':'lake-root','path':str(source/'build.tar'),'if-no-files-found':'error'}},context)
        destination=self.root/'unpack'
        run.action({'name':'download','uses':'actions/download-artifact@pin',
                    'with':{'name':'lake-root','path':str(destination)}},context)
        self.assertEqual((destination/'build.tar').read_bytes(),b'produced by workflow')

    def test_dependency_cycle_and_missing_github_evidence_fail_closed(self):
        workflow=self.workflow([],name='first',needs=['second'])
        workflow['jobs']['second']={'runs-on':self.runner_name,'needs':['first'],'steps':[]}
        run=runner.WorkflowRun(workflow,self.artifacts,self.snapshot)
        with self.assertRaisesRegex(ValueError,'cyclic local CI artifact dependency'):run.run('first')
        workflow=self.workflow([],name='all-checks')
        with self.assertRaisesRegex(ValueError,r'GitHub needs\.\*\.result evidence'):
            runner.WorkflowRun(workflow,self.artifacts,self.snapshot).run('all-checks')

    def test_wrong_native_runner_never_relabelled(self):
        workflow=self.workflow([{'name':'native','run':'touch wrong-platform'}])
        workflow['jobs']['sample']['runs-on']='ubuntu-24.04' if self.runner_name!='ubuntu-24.04' else 'ubuntu-24.04-arm'
        with self.assertRaisesRegex(ValueError,'requires .* actual platform'):
            self.run_row(workflow)
        self.assertFalse((self.root/'wrong-platform').exists())

    def test_conditions_and_unsupported_expressions(self):
        values={'success':True,'failure':False,'env.AIR2LEAN_REUSED':'','matrix.zig':'0.17.0'}
        self.assertTrue(runner.expression("${{ !env.AIR2LEAN_REUSED && (matrix.zig != '0.16.0' || failure()) }}",values))
        for expression in ('success() &&',"unknown()", "'missing parenthesis' && ("):
            with self.assertRaises(ValueError):runner.expression(expression,values)

    def test_status_function_text_inside_literal_is_unchanged(self):
        self.assertTrue(runner.expression("env.MODE == 'failure()'",{'env.MODE':'failure()'}))
        self.assertFalse(runner.expression("env.MODE != 'failure()'",{'env.MODE':'failure()'}))

    def test_unsupported_checkout_options_and_false_installer_guard_fail_closed(self):
        workflow=self.workflow([{'name':'Checkout','uses':'actions/checkout@pin','with':{'ref':'other'}}])
        with self.assertRaisesRegex(ValueError,'unsupported actions/checkout options'):self.run_row(workflow)
        job={'steps':[{'name':'Install elan','if':False,'run':'unqualified installer'}]}
        with self.assertRaisesRegex(ValueError,'changed optimized CI substitution'):runner.validate_job(job,True)

    def test_whole_checkout_declaration_schema_and_unknown_fields_are_checked(self):
        path=self.root/'.github/ci-inputs.json'
        for data in ({'schema':'wrong','parts':{'sample':{'reuse':False}}},
                     {'schema':'air2lean-ci-inputs/2','parts':{'sample':{'reuse':False,'typo':1}}}):
            path.write_text(json.dumps(data))
            with self.assertRaises(ValueError):runner.restrict_part('sample')

    def test_snapshot_identity_survives_clock_and_caller_git_date_changes(self):
        files={'README.md':b'tested source\n'}
        stream=io.BytesIO()
        with tarfile.open(fileobj=stream,mode='w') as archive:
            for name,content in files.items():
                info=tarfile.TarInfo(name);info.size=len(content);archive.addfile(info,io.BytesIO(content))
        (self.snapshot/'files').write_bytes(b'README.md\0')
        work=self.root/'work';work.mkdir();os.chdir(work)
        identities=[]
        for date in ('2001-01-01T00:00:00Z','2026-10-17T00:00:00Z'):
            with patch.dict(os.environ,GIT_AUTHOR_DATE=date,GIT_COMMITTER_DATE=date):
                runner.reset_checkout(self.snapshot,stream.getvalue())
            identities.append(runner.reuse_helpers().GENERATED.head_identity(work))
        self.assertEqual(identities[0],identities[1])

    def test_failed_step_keeps_diagnostic_upload_and_final_failure(self):
        workflow=self.workflow([
            {'name':'failure','run':'printf evidence > "$RUNNER_TEMP/failure.txt"; exit 8'},
            {'name':'normal follow-up','run':'touch should-not-run'},
            {'name':'failure evidence','if':'${{ failure() && !cancelled() }}',
             'uses':'actions/upload-artifact@pin','with':{'name':'diagnostic','path':'${{ runner.temp }}/failure.txt','if-no-files-found':'error'}}])
        with self.assertRaisesRegex(ValueError,'workflow steps failed'):self.run_row(workflow)
        self.assertFalse((self.root/'should-not-run').exists())
        self.assertEqual((self.artifacts/'uploads/diagnostic/failure.txt').read_text(),'evidence')
        self.assertFalse(json.loads((self.artifacts/'sample/row.json').read_text())['success'])

    def test_discovery_accumulates_reads_and_executes_later_steps(self):
        workflow=self.workflow([{'name':'first','run':'true'},
                                {'name':'later','run':'printf later > "$RUNNER_TEMP/later"'}])
        run=runner.WorkflowRun(workflow,self.artifacts,self.snapshot,discover=True)
        original=runner.call
        def call(command,**kwargs):
            if command[-2:]==['check-restricted','--reset']:
                raise subprocess.CalledProcessError(1,command)
            return original(command,**kwargs)
        with patch.object(runner,'call',side_effect=call),self.assertRaisesRegex(ValueError,'workflow steps failed'):
            run.run_row('sample','sample',{})
        self.assertEqual((self.artifacts/'sample/later').read_text(),'later')
        report=json.loads((self.artifacts/'sample/row.json').read_text())
        self.assertTrue(all(step['undeclared_reads'] for step in report['steps']))

    def test_host_filters_recipe_overrides_and_children_inherit_lock(self):
        tools=self.root/'tools';tools.mkdir();(self.artifacts/'work').mkdir()
        def inspect(selected):
            self.assertEqual(selected,'sample')
            self.assertNotIn('AIR2LEAN_EXAMPLES',os.environ)
            self.assertNotIn('AIR2LEAN_ZIG_AIR',os.environ)
            self.assertEqual(os.environ['AIR2LEAN_CAS_DIR'],'shared-cas')
            self.assertEqual(os.environ['AIR2LEAN_JOBS'],'2')
            self.assertEqual(os.environ['AIR2LEAN_MEM_MIB'],'11000')
            descriptor=runner.CACHE_LOCK_FD
            runner.call([sys.executable,'-c',f'import os;os.fstat({descriptor})'])
        fake=SimpleNamespace(run=inspect)
        with patch.dict(os.environ,PATH='/usr/bin:/bin',AIR2LEAN_LOCAL_HOST_TOOLS=str(tools),
                        AIR2LEAN_LOCAL_ARTIFACTS=str(self.artifacts),AIR2LEAN_LOCAL_SNAPSHOT=str(self.snapshot),
                        AIR2LEAN_EXAMPLES='basic',AIR2LEAN_ZIG_AIR='/foreign/compiler',AIR2LEAN_CAS_DIR='shared-cas',
                        AIR2LEAN_JOBS='2',AIR2LEAN_MEM_MIB='11000'),\
             patch.object(runner,'WorkflowRun',return_value=fake):
            runner.run_host({},'part','sample')
        self.assertIsNone(runner.CACHE_LOCK_FD)

    def test_cancellation_drains_owned_group_before_releasing_cache_lock(self):
        import fcntl
        import select
        import signal
        import time

        # The intermediary drops the lock FD. Its descendant ignores TERM and keeps
        # stdout open, so EOF establishes that group cleanup reached the descendant.
        grandchild="""import json,os,signal,sys,time
signal.signal(signal.SIGTERM,signal.SIG_IGN)
try:
    os.fstat(int(sys.argv[1])); lock_fd_open=True
except OSError:
    lock_fd_open=False
print(json.dumps(dict(pid=os.getpid(),lock_fd_open=lock_fd_open)),flush=True)
time.sleep(60)
"""
        leader=("import json,os,subprocess,sys,time; "
                "print(json.dumps(dict(leader_pid=os.getpid())),flush=True); "
                "subprocess.Popen([sys.executable,'-B','-c',"+repr(grandchild)+",sys.argv[1]]); time.sleep(60)")
        worker="""import fcntl,importlib.util,signal,sys
module_path,lock_path,leader=sys.argv[1:]
spec=importlib.util.spec_from_file_location('runner',module_path)
runner=importlib.util.module_from_spec(spec); spec.loader.exec_module(runner)
lock=open(lock_path,'a'); fcntl.flock(lock,fcntl.LOCK_EX)
runner.CACHE_LOCK_FD=lock.fileno()
signal.signal(signal.SIGTERM,runner.stop)
try:
    runner.call([sys.executable,'-B','-c',leader,str(lock.fileno())])
except runner.Cancelled as error:
    raise SystemExit(128+error.signum)
"""
        lock_path=self.root/'cancel-cache.lock'
        process=subprocess.Popen([sys.executable,'-B','-c',worker,
                                  str(ROOT/'scripts/local-ci-steps.py'),str(lock_path),leader],
                                 stdout=subprocess.PIPE,bufsize=0)
        leader_pid=descendant=None
        cleaned=False
        try:
            self.assertTrue(select.select([process.stdout],[],[],5)[0],'leader did not announce readiness')
            leader_pid=json.loads(process.stdout.readline())['leader_pid']
            self.assertTrue(select.select([process.stdout],[],[],5)[0],'descendant did not announce readiness')
            details=json.loads(process.stdout.readline());descendant=details['pid']
            self.assertFalse(details['lock_fd_open'])
            os.kill(process.pid,signal.SIGTERM)
            with lock_path.open('a') as probe,self.assertRaises(BlockingIOError):
                fcntl.flock(probe,fcntl.LOCK_EX|fcntl.LOCK_NB)
            time.sleep(0.25)
            os.kill(process.pid,signal.SIGTERM)
            with lock_path.open('a') as probe,self.assertRaises(BlockingIOError):
                fcntl.flock(probe,fcntl.LOCK_EX|fcntl.LOCK_NB)
            self.assertEqual(process.wait(timeout=5),143)
            self.assertTrue(select.select([process.stdout],[],[],0.5)[0],
                            'surviving descendant still holds stdout')
            self.assertEqual(process.stdout.read(1),b'')
            with lock_path.open('a') as probe:
                fcntl.flock(probe,fcntl.LOCK_EX|fcntl.LOCK_NB)
            cleaned=True
        finally:
            if not cleaned:
                for pid in (descendant,leader_pid):
                    if pid is not None:
                        try:os.kill(pid,signal.SIGKILL)
                        except ProcessLookupError:pass
            if process.poll() is None:process.kill()
            process.wait(timeout=5)
            process.stdout.close()

    def test_snapshot_reset_removes_check_tree_but_preserves_facets_and_symlink_target(self):
        stream=io.BytesIO();content=b'tested source\n'
        with tarfile.open(fileobj=stream,mode='w') as archive:
            info=tarfile.TarInfo('README.md');info.size=len(content)
            archive.addfile(info,io.BytesIO(content))
        (self.snapshot/'files').write_bytes(b'README.md\0')
        work=self.root/'work';work.mkdir();os.chdir(work)
        facet=work/'.lake/build/lib/lean/Proofs/Basic.olean'
        facet.parent.mkdir(parents=True);facet.write_bytes(b'incremental build facet')
        outside=self.root/'outside';outside.mkdir()
        sentinel=outside/'private-source.lean';sentinel.write_bytes(b'outside source')
        check_tree=work/'.lake/check-tree'
        for symlink in (False,True):
            with self.subTest(symlink=symlink):
                if symlink:
                    check_tree.symlink_to(outside,target_is_directory=True)
                else:
                    check_tree.mkdir();(check_tree/'withheld-source.lean').write_bytes(b'previous whole tree')
                runner.reset_checkout(self.snapshot,stream.getvalue())
                self.assertFalse(os.path.lexists(check_tree))
                self.assertEqual(facet.read_bytes(),b'incremental build facet')
                self.assertEqual(sentinel.read_bytes(),b'outside source')

    def test_snapshot_reset_removes_previous_compilers_without_following_symlinks(self):
        stream=io.BytesIO();content=b'tested source\n'
        with tarfile.open(fileobj=stream,mode='w') as archive:
            info=tarfile.TarInfo('README.md');info.size=len(content)
            archive.addfile(info,io.BytesIO(content))
        (self.snapshot/'files').write_bytes(b'README.md\0')
        work=self.root/'work';work.mkdir();os.chdir(work)
        outside=self.root/'outside';outside.mkdir()
        sentinel=outside/'removed-from-next-version.zig';sentinel.write_bytes(b'outside compiler')
        compilers=('host-zig','zig-air-0.14.1','zig-air-0.17.0')
        for symlink in (False,True):
            with self.subTest(symlink=symlink):
                for name in compilers:
                    target=work/name
                    if symlink:
                        target.symlink_to(outside,target_is_directory=True)
                    else:
                        target.mkdir();(target/sentinel.name).write_bytes(b'stale compiler file')
                runner.reset_checkout(self.snapshot,stream.getvalue())
                for name in compilers:
                    self.assertFalse(os.path.lexists(work/name))
                self.assertEqual(sentinel.read_bytes(),b'outside compiler')
                self.assertEqual((work/'README.md').read_bytes(),content)

    def test_release_planner_still_excludes_supplied_test_recipes(self):
        _,excluded=runner.reuse_helpers().RR.local_ci_helpers((ROOT/'scripts/local-ci-steps.py').read_text())
        self.assertTrue({'Unpack the patched zig','Unpack the Lake build','Install the generated files',
                         'Install system packages','Install elan','Install host zig'}<=excluded)

    def test_changed_supplied_recipe_and_unknown_download_fail_before_conditions(self):
        original={'name':'Unpack the Lake build','if':'${{ !env.AIR2LEAN_REUSED }}',
                  'run':'tar --zstd -xf "$RUNNER_TEMP/lake-root/lake-root.tar.zst"'}
        runner.validate_job({'steps':[original]},True)
        for step in (original|{'run':'echo changed'},original|{'if':False},
                     {'name':'Download unqualified input','uses':'actions/download-artifact@pin',
                      'with':{'name':'external','path':'target'}}):
            with self.assertRaisesRegex(ValueError,'qualification|unsupported optimized'):
                runner.validate_job({'steps':[step]},True)

    def test_arm_image_does_not_apply_rosetta_python_hook(self):
        dockerfile=(ROOT/'Dockerfile.local-ci').read_text()
        guards=re.findall(r'if (\[ "\$PYTHON_ARCH" = arm64 \].*?); then',dockerfile)
        self.assertEqual(len(guards),2)
        for actual,expected in [('arm64','native'),('amd64','rosetta')]:
            for guard in guards:
                command=f'dpkg() {{ printf %s {actual}; }}; PYTHON_ARCH=arm64; if {guard}; then printf rosetta; else printf native; fi'
                result=subprocess.run(['bash','-c',command],check=True,text=True,stdout=subprocess.PIPE)
                self.assertEqual(result.stdout,expected)


if __name__=='__main__':unittest.main()
