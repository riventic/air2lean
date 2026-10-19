#!/usr/bin/env python3
"""Cache, source-capture and workflow-adapter regressions; no toolchain builds or containers."""
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import runpy
import shlex
import shutil
import stat
import subprocess
import sys
import tarfile
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[3]
spec=importlib.util.spec_from_file_location('local_ci_steps',ROOT/'scripts/local-ci-steps.py')
runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
prune=runner.prune_stale_modules

def isolate_git_environment(test):
    environment={key:value for key,value in os.environ.items() if not key.startswith('GIT_')}
    environment.update(GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL=os.devnull)
    clean_environment=patch.dict(os.environ,environment,clear=True)
    clean_environment.start();test.addCleanup(clean_environment.stop)

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
        self.snapshot=self.root/'snapshot';self.snapshot.mkdir()
        source=b'tested snapshot'
        (self.snapshot/'source.tar').write_bytes(source)
        (self.snapshot/'files').write_bytes(b'')
        self.source_stamp='revision=test\ntracked_clean=yes\nsnapshot_sha256='+hashlib.sha256(source).hexdigest()+'\n'
        for directory in (self.artifacts,self.snapshot):
            (directory/'source-revision').write_text(self.source_stamp)
        (self.root/'.github').mkdir()
        (self.root/'.github/workflows').mkdir()
        (self.root/'.github/workflows/ci.yml').write_text('tested workflow\n')
        (self.root/'scripts').mkdir()
        (self.root/'scripts/ci-reuse.py').write_text('raise SystemExit(0)\n')
        self.previous=Path.cwd();os.chdir(self.root);self.addCleanup(os.chdir,self.previous)
        isolate_git_environment(self)
        subprocess.run(['git','init','-q','--object-format=sha1'],check=True,capture_output=True)
        self.runner_name='macos-14' if sys.platform=='darwin' else {'x86_64':'ubuntu-24.04','aarch64':'ubuntu-24.04-arm'}[os.uname().machine]

    def commit(self):
        subprocess.run(['git','add','-f','--','.'],check=True,capture_output=True)
        subprocess.run(['git','-c','user.name=workflow test','-c','user.email=workflow@example.invalid',
                        'commit','--allow-empty','-qm','workflow fixture'],check=True,capture_output=True)

    def workflow(self,steps,name='sample',**fields):
        (self.snapshot/'source.tar').write_bytes(b'tested snapshot')
        (self.snapshot/'files').write_bytes(b'')
        job={'runs-on':self.runner_name,'steps':steps}|fields
        (self.root/'.github/ci-inputs.json').write_text(json.dumps({'schema':'air2lean-ci-inputs/2','parts':{name:{'reuse':False}}}))
        self.commit()
        return {'jobs':{name:job}}

    def run_row(self,workflow,name='sample'):
        run=runner.WorkflowRun(workflow,self.artifacts,self.snapshot)
        run.run_row(name,name,{})
        return json.loads((self.artifacts/name/'row.json').read_text())

    def reset_fixture(self):
        stream=io.BytesIO();content=b'tested source\n'
        with tarfile.open(fileobj=stream,mode='w') as archive:
            info=tarfile.TarInfo('README.md');info.size=len(content)
            archive.addfile(info,io.BytesIO(content))
        (self.snapshot/'files').write_bytes(b'README.md\0')
        work=self.root/'work';work.mkdir();os.chdir(work)
        return work,stream.getvalue(),content

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
        self.assertEqual(report['source'],self.source_stamp)
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

    def test_job_conditions_fail_closed_before_running_commands(self):
        for index,condition in enumerate((False,'github.ref')):
            name=f'conditional-{index}'
            workflow=self.workflow([{'name':'must not run','run':'touch unsafe'}],
                                   name=name,**{'if':condition})
            with self.subTest(condition=condition),self.assertRaisesRegex(ValueError,'job-level CI condition'):
                self.run_row(workflow,name)
            self.assertFalse((self.root/'unsafe').exists())
            self.assertFalse(json.loads((self.artifacts/name/'row.json').read_text())['success'])

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

    def test_artifact_names_cannot_escape_upload_namespace(self):
        workflow=self.workflow([])
        run=runner.WorkflowRun(workflow,self.artifacts,self.snapshot)
        source=self.root/'source-revision';source.write_text('must not replace evidence')
        for name in ('.','..'):
            with self.subTest(name=name),self.assertRaisesRegex(ValueError,'unsafe CI artifact name'):
                run.action({'name':'upload','uses':'actions/upload-artifact@pin',
                            'with':{'name':name,'path':str(source)}},{})
            self.assertEqual((self.artifacts/'source-revision').read_text(),self.source_stamp)

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
        values={'env.AIR2LEAN_REUSED':'','matrix':{'zig':'0.17.0'}}
        self.assertTrue(runner.TM.condition("${{ !env.AIR2LEAN_REUSED && (matrix.zig != '0.16.0' || failure()) }}",values))
        for expression in ('success() &&',"unknown()", "'missing parenthesis' && ("):
            with self.assertRaises(runner.TM.Unknown):runner.TM.condition(expression,values)

    def test_status_function_text_inside_literal_is_unchanged(self):
        self.assertTrue(runner.TM.condition("env.MODE == 'failure()'",{'env.MODE':'failure()'}))
        self.assertFalse(runner.TM.condition("env.MODE != 'failure()'",{'env.MODE':'failure()'}))

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
            self.commit()
            with self.assertRaises(ValueError):runner.restrict_part('sample')

    def test_snapshot_identity_survives_clock_and_caller_git_date_changes(self):
        work,source,_content=self.reset_fixture()
        identities=[]
        for date in ('2001-01-01T00:00:00Z','2026-10-17T00:00:00Z'):
            with patch.dict(os.environ,GIT_AUTHOR_DATE=date,GIT_COMMITTER_DATE=date):
                runner.reset_checkout(self.snapshot,source)
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
                                {'name':'later','run':'printf later > "$RUNNER_TEMP/later"'}],
                               **{'runs-on':'ubuntu-24.04'})
        run=runner.WorkflowRun(workflow,self.artifacts,self.snapshot,discover=True)
        original=runner.call
        def call(command,**kwargs):
            if command[-2:]==['check-restricted','--reset']:
                raise subprocess.CalledProcessError(1,command)
            return original(command,**kwargs)
        actual=os.uname()
        linux=os.uname_result(('Linux',actual.nodename,actual.release,actual.version,'x86_64'))
        with patch.object(runner,'call',side_effect=call),patch.object(sys,'platform','linux'),\
             patch.object(os,'uname',return_value=linux),self.assertRaisesRegex(ValueError,'workflow steps failed'):
            run.run_row('sample','sample',{})
        self.assertEqual((self.artifacts/'sample/later').read_text(),'later')
        report=json.loads((self.artifacts/'sample/row.json').read_text())
        self.assertTrue(all(step['undeclared_reads'] for step in report['steps']))

    def test_host_restricted_request_is_rejected_before_commands(self):
        workflow=self.workflow([{'name':'must not run','run':'touch unsafe'}],**{'runs-on':'macos-14'})
        run=runner.WorkflowRun(workflow,self.artifacts,self.snapshot,restricted=True)
        actual=os.uname()
        host=os.uname_result(('Darwin',actual.nodename,actual.release,actual.version,'arm64'))
        with patch.object(sys,'platform','darwin'),patch.object(os,'uname',return_value=host),\
             patch.object(runner,'restrict_part') as restrict,\
             self.assertRaisesRegex(ValueError,'restricted host qualification is unavailable'):
            run.run_row('sample','sample',{})
        restrict.assert_not_called();self.assertFalse((self.root/'unsafe').exists())
        report=json.loads((self.artifacts/'sample/row.json').read_text())
        self.assertFalse(report['success'])
        self.assertEqual(report['restriction'],{'requested':True,'qualified':False,'files_withheld':False,
                                                'gap':runner.HOST_SOURCE_GAP})

    def test_linux_receipts_distinguish_actual_restriction_and_discovery(self):
        for discover in (False,True):
            with self.subTest(discover=discover):
                fixture=Workflow();fixture.setUp()
                try:
                    (fixture.root/'README.md').write_text('private source\n')
                    workflow=fixture.workflow([],**{'runs-on':'ubuntu-24.04'})
                    run=runner.WorkflowRun(workflow,fixture.artifacts,fixture.snapshot,discover=discover)
                    inputs=runner.CR.Inputs(['**'],exclude=['README.md'])
                    if discover:
                        runner.CR.discover(fixture.root,inputs,'sample')
                    else:
                        runner.CR.restrict(fixture.root,inputs,'sample')
                    self.assertEqual(runner.CR.check_restricted(fixture.root),[])
                    actual=os.uname()
                    linux=os.uname_result(('Linux',actual.nodename,actual.release,actual.version,'x86_64'))
                    with patch.object(sys,'platform','linux'),patch.object(os,'uname',return_value=linux):
                        run.run_row('sample','sample',{})
                    report=json.loads((fixture.artifacts/'sample/row.json').read_text())
                    self.assertEqual(report['restriction'],{'requested':False,'qualified':not discover,
                                                            'files_withheld':not discover})
                finally:
                    fixture.doCleanups()

    def test_support_discovery_rejects_intrinsic_restriction_before_commands(self):
        workflow=self.workflow([{'name':'support restriction',
                                 'run':'python3 scripts/ci-reuse.py restrict --support lake --seal\ntouch unsafe'}],
                               name='lake',**{'runs-on':'ubuntu-24.04'})
        run=runner.WorkflowRun(workflow,self.artifacts,self.snapshot,discover=True)
        actual=os.uname()
        linux=os.uname_result(('Linux',actual.nodename,actual.release,actual.version,'x86_64'))
        with patch.object(sys,'platform','linux'),patch.object(os,'uname',return_value=linux),\
             self.assertRaisesRegex(ValueError,'support workflow enforces its own restricted checkout'):
            run.run_row('lake','lake',{})
        self.assertFalse((self.root/'unsafe').exists())
        report=json.loads((self.artifacts/'lake/row.json').read_text())
        self.assertFalse(report['success']);self.assertFalse(report['restriction']['qualified'])

    def test_host_discovery_withholds_nothing_and_records_the_source_gap(self):
        (self.root/'README.md').write_text('unrestricted source\n')
        workflow=self.workflow([{'name':'native diagnostic','run':'test "$(cat README.md)" = "unrestricted source"'}],
                               **{'runs-on':'macos-14'})
        (self.root/'.github/ci-inputs.json').write_text(json.dumps(
            {'schema':'air2lean-ci-inputs/2','parts':{'sample':{'inputs':['scripts/**']}}}))
        self.commit()
        run=runner.WorkflowRun(workflow,self.artifacts,self.snapshot,discover=True)
        actual=os.uname()
        host=os.uname_result(('Darwin',actual.nodename,actual.release,actual.version,'arm64'))
        with patch.object(sys,'platform','darwin'),patch.object(os,'uname',return_value=host),\
             patch.object(runner,'restrict_part') as restrict:
            run.run_row('sample','sample',{})
        restrict.assert_not_called()
        report=json.loads((self.artifacts/'sample/row.json').read_text())
        self.assertTrue(report['success'])
        self.assertEqual(report['restriction'],{'requested':False,'qualified':False,'files_withheld':False,
                                                'gap':runner.HOST_SOURCE_GAP})
        self.assertIn('git -C ../../../.. show HEAD:README.md',report['restriction']['gap'])
        self.assertEqual((self.root/'README.md').read_text(),'unrestricted source\n')

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
              patch.object(runner,'WorkflowRun',return_value=fake) as factory:
            runner.run_host({},'part','sample')
        factory.assert_called_once_with({},self.artifacts,str(self.snapshot),False,restricted=True)
        self.assertIsNone(runner.CACHE_LOCK_FD)

    def test_cancellation_at_child_launch_drains_the_started_process(self):
        import signal

        original=subprocess.Popen;started=[]
        def launch(*args,**kwargs):
            child=original(*args,**kwargs)
            if args[0][0]==sys.executable:
                started.append(child)
                runner.stop(signal.SIGTERM,None)  # The constructor-return cancellation boundary.
            return child
        try:
            with patch.object(subprocess,'Popen',side_effect=launch),self.assertRaises(runner.Cancelled):
                runner.call([sys.executable,'-B','-c','import time;time.sleep(60)'])
            self.assertEqual(len(started),1)
            self.assertIsNotNone(started[0].poll(),'child survived cancellation before the wait')
        finally:
            for child in started:
                if child.poll() is None:child.kill()
                child.wait(timeout=5)

    def test_cancellation_at_reap_does_not_signal_a_released_pid(self):
        import signal

        original=subprocess.Popen;started=[]
        def launch(*args,**kwargs):
            child=original(*args,**kwargs)
            if args[0][0]==sys.executable:
                wait=child.wait;started.append((child,wait))
                def reap(*args,**kwargs):
                    status=wait(*args,**kwargs)
                    runner.stop(signal.SIGTERM,None)
                    return status
                child.wait=reap
            return child
        try:
            with patch.object(subprocess,'Popen',side_effect=launch),\
                 patch.object(runner,'stop_group') as stop_group,\
                 self.assertRaises(runner.Cancelled):
                runner.call([sys.executable,'-B','-c','pass'])
            self.assertEqual(len(started),1)
            self.assertEqual(started[0][0].returncode,0)
            stop_group.assert_not_called()
            self.assertIsNone(runner.PENDING_SIGNAL)
        finally:
            for child,wait in started:
                if child.poll() is None:child.kill()
                wait(timeout=5)

    def test_cancellation_drains_owned_group_before_releasing_cache_lock(self):
        import fcntl
        import select
        import signal

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
forward=runner.GUARD.signal_workload
def synchronized_cleanup(child,tree,signum):
    forward(child,tree,signum)
    if signum==signal.SIGTERM:
        print('cleanup-ready',flush=True)
        sys.stdin.readline()
runner.GUARD.signal_workload=synchronized_cleanup
try:
    runner.call([sys.executable,'-B','-c',leader,str(lock.fileno())])
except runner.Cancelled as error:
    raise SystemExit(128+error.signum)
"""
        lock_path=self.root/'cancel-cache.lock'
        process=subprocess.Popen([sys.executable,'-B','-c',worker,
                                  str(ROOT/'scripts/local-ci-steps.py'),str(lock_path),leader],
                                 stdin=subprocess.PIPE,stdout=subprocess.PIPE,bufsize=0)
        cleaned=False
        sample_budget=runner.GUARD.PS_TIMEOUT+5
        try:
            self.assertTrue(select.select([process.stdout],[],[],5)[0],'leader did not announce readiness')
            self.assertGreater(json.loads(process.stdout.readline())['leader_pid'],0)
            self.assertTrue(select.select([process.stdout],[],[],5)[0],'descendant did not announce readiness')
            details=json.loads(process.stdout.readline());self.assertGreater(details['pid'],0)
            self.assertFalse(details['lock_fd_open'])
            os.kill(process.pid,signal.SIGTERM)
            self.assertTrue(select.select([process.stdout],[],[],sample_budget)[0],'cleanup did not announce readiness')
            self.assertEqual(process.stdout.readline(),b'cleanup-ready\n')
            with lock_path.open('a') as probe,self.assertRaises(BlockingIOError):
                fcntl.flock(probe,fcntl.LOCK_EX|fcntl.LOCK_NB)
            os.kill(process.pid,signal.SIGTERM)
            with lock_path.open('a') as probe,self.assertRaises(BlockingIOError):
                fcntl.flock(probe,fcntl.LOCK_EX|fcntl.LOCK_NB)
            process.stdin.write(b'continue\n');process.stdin.flush()
            self.assertEqual(process.wait(timeout=sample_budget+2),143)
            self.assertTrue(select.select([process.stdout],[],[],0.5)[0],
                            'surviving descendant still holds stdout')
            self.assertEqual(process.stdout.read(1),b'')
            with lock_path.open('a') as probe:
                fcntl.flock(probe,fcntl.LOCK_EX|fcntl.LOCK_NB)
            cleaned=True
        finally:
            if not cleaned and process.poll() is None:
                # The worker retains its own leader anchor and knows the entire
                # group even when a descendant never announced its PID here.
                try:
                    process.stdin.write(b'continue\n');process.stdin.flush()
                except BrokenPipeError:
                    pass
                try:os.kill(process.pid,signal.SIGTERM)
                except ProcessLookupError:pass
                process.wait(timeout=2*runner.GUARD.PS_TIMEOUT+7)
            process.stdin.close()
            process.stdout.close()

    def test_snapshot_reset_removes_check_tree_but_preserves_facets_and_symlink_target(self):
        work,source,_content=self.reset_fixture()
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
                runner.reset_checkout(self.snapshot,source)
                self.assertFalse(os.path.lexists(check_tree))
                self.assertEqual(facet.read_bytes(),b'incremental build facet')
                self.assertEqual(sentinel.read_bytes(),b'outside source')

    def test_snapshot_reset_removes_previous_compilers_without_following_symlinks(self):
        work,source,content=self.reset_fixture()
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
                runner.reset_checkout(self.snapshot,source)
                for name in compilers:
                    self.assertFalse(os.path.lexists(work/name))
                self.assertEqual(sentinel.read_bytes(),b'outside compiler')
                self.assertEqual((work/'README.md').read_bytes(),content)

    def test_release_planner_still_excludes_supplied_test_recipes(self):
        excluded=runner.reuse_helpers().RR.local_ci_helpers((ROOT/'scripts/local-ci-steps.py').read_text())
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
        isolate_git_environment(self)
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

    def test_all_marked_cache_trees_are_removed_at_arbitrary_depths(self):
        trees=[]
        for cache in ('.lake','tests/diff/.lake'):
            for name in ('previous-full/source-copy','another-name'):
                tree=self.repo/cache/name;trees.append(tree)
                self.write(str(tree.relative_to(self.repo)/'.air2lean-check-tree.json'),b'')
                self.write(str(tree.relative_to(self.repo)/'withheld.txt'),b'old unrestricted bytes')
                self.write(str(tree.relative_to(self.repo)/'nested/.air2lean-check-tree.json'),b'{}')
        facet=self.write('.lake/build/lib/lean/Current.olean',b'keep Lake facet')
        self.seal()
        for tree in trees:self.assertFalse(tree.exists(),str(tree))
        self.assertEqual(facet.read_bytes(),b'keep Lake facet')

    def test_marked_cache_root_and_symlink_marker_fail_closed(self):
        marker=self.write('.lake/.air2lean-check-tree.json',b'{}')
        self.seal(error='Lake cache root is a marked source tree');marker.unlink()
        external=self.root/'marker-target';external.write_bytes(b'outside data')
        marker=self.repo/'.lake/any-source/.air2lean-check-tree.json'
        marker.parent.mkdir();marker.symlink_to(external)
        self.seal(error='unsupported source-tree marker type')
        self.assertEqual(external.read_bytes(),b'outside data')

    def test_cache_walk_errors_are_not_silently_skipped(self):
        self.write('.lake/other/withheld.txt',b'old source bytes')
        def unreadable(*_args,**kwargs):
            kwargs['onerror'](PermissionError('unreadable cache subtree'))
        with patch.object(os,'fwalk',side_effect=unreadable):
            self.seal(error='unreadable cache subtree')

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
          [ "$SHARED_CONTEXT" = "$GITHUB_WORKSPACE/isolation" ]
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
        for name in ('ci-reuse.py','release-record.py','generated.py','target-matrix.py','cas.py','build-guard.py'):
            self.write('scripts/'+name,(ROOT/'scripts'/name).read_bytes())
        self.write('lean-toolchain',(ROOT/'lean-toolchain').read_bytes())
        self.write('lakefile.toml',b'name = "local_ci_isolation"\n')
        self.write('withheld.txt',b'unique committed source canary\n')
        self.commit();self.pinned=self.revision()
        parsed=runner.TM.parse_workflow_yaml(workflow)
        self.capture()
        return parsed

    def run_part_interpreter(self,workflow=None,local_mode='part'):
        from contextlib import nullcontext

        actual_popen=subprocess.Popen;executed=[];decoded=[]
        def decode(text):
            # Expression controls inject decoded DATA at the canonical reader boundary;
            # separate controls below use the actual reader on real captured YAML.
            decoded.append(text)
            return workflow
        def popen(command,*args,**kwargs):
            executed.append(command)
            if command==['bash','scripts/local-ci.sh','--prepare','0.17.0']:
                command=[sys.executable,'-B','-c','pass']
            # The host test has no container cache lock on FD9. All Git and protected
            # shell commands still execute normally in their own process groups.
            if 'pass_fds' in kwargs:kwargs['pass_fds']=()
            return actual_popen(command,*args,**kwargs)
        recovery=self.root/'recovered-source'
        actual_uname=os.uname()
        linux=os.uname_result(('Linux',actual_uname.nodename,actual_uname.release,
                               actual_uname.version,'x86_64'))
        reader=patch.object(runner.TM,'parse_workflow_yaml',decode) if workflow is not None else nullcontext()
        # This unit fixture exercises the Linux part adapter on any development host;
        # all Git, restriction and protected shell commands still execute for real.
        with reader,patch.object(subprocess,'Popen',popen),\
             patch.object(sys,'platform','linux'),patch.object(os,'uname',return_value=linux),\
             patch.dict(os.environ,ELAN_HOME=str(self.root/'elan'),AIR2LEAN_TEST_HEAD=self.pinned,
                        AIR2LEAN_TEST_ARCHIVE=str(self.snapshot/'source.tar'),
                         AIR2LEAN_TEST_RECOVERY=str(recovery),AIR2LEAN_LOCAL_MODE=local_mode,
                        AIR2LEAN_LOCAL_ARTIFACTS=str(self.artifacts),
                        AIR2LEAN_LOCAL_SNAPSHOT=str(self.snapshot)):
            runner.main(['part','test/0.17.0/isolation'])
        if workflow is not None:self.assertEqual(len(decoded),1,'decoded-DATA expression fixture was not consumed once')
        return executed,recovery

    def test_actual_part_interpreter_seals_original_git_objects_before_protected_step(self):
        workflow=self.part_fixture()
        # This is the precise recovery route the actual protected step attempts later.
        self.assertEqual(self.git('show',self.pinned+':withheld.txt'),b'unique committed source canary\n')
        with tarfile.open(self.snapshot/'source.tar') as archive:
            self.assertEqual(archive.extractfile('withheld.txt').read(),b'unique committed source canary\n')
        executed,recovery=self.run_part_interpreter(workflow)
        self.assertTrue(recovery.exists());self.assertEqual(recovery.read_bytes(),b'')
        self.assertIn(['python3','scripts/ci-reuse.py','restrict','--part','test/0.17.0/isolation','--seal'],executed)
        with self.assertRaises(subprocess.CalledProcessError):
            self.git('show',self.pinned+':withheld.txt')

    def test_actual_part_request_restricts_without_wrapper_mode_environment(self):
        workflow=self.part_fixture()
        executed,_recovery=self.run_part_interpreter(workflow,local_mode='')
        self.assertIn(['python3','scripts/ci-reuse.py','restrict','--part','test/0.17.0/isolation','--seal'],executed)
        report=json.loads((self.artifacts/'test-0.17.0-isolation/row.json').read_text())
        self.assertEqual(report['restriction'],{'requested':True,'qualified':True,'files_withheld':True})

    def test_actual_bad_restriction_metadata_retains_the_failed_row_receipt(self):
        workflow=self.part_fixture()
        workflow['jobs']['test']['steps'][0]['run'] = (
            'printf malformed > "$(git rev-parse --git-dir)/air2lean-restricted.json"\n'
            +workflow['jobs']['test']['steps'][0]['run'])
        with self.assertRaises(subprocess.CalledProcessError):
            self.run_part_interpreter(workflow)
        report=json.loads((self.artifacts/'test-0.17.0-isolation/row.json').read_text())
        self.assertFalse(report['success']);self.assertFalse(report['restriction']['qualified'])
        self.assertIn('check-restricted',report['error'])
        self.assertIn('cannot read restriction state',report['restriction']['error'])

    def test_action_logs_stay_outside_the_legacy_release_gate_stream(self):
        import ast
        from contextlib import redirect_stdout

        self.part_fixture()
        path=self.repo/'.github/workflows/ci.yml'
        path.write_text(path.read_text().replace('    steps:\n',
            '    steps:\n      - name: Checkout\n        uses: actions/checkout@pin\n'))
        self.commit();self.pinned=self.revision();self.capture()
        output=io.StringIO()
        with redirect_stdout(output):self.run_part_interpreter()
        headers=[match for line in output.getvalue().splitlines()
                 if (match:=runner.CR.RR.HEADER.fullmatch(line))]
        self.assertEqual([match[2] for match in headers],['Original Git source must be unavailable'])
        self.assertEqual(ast.literal_eval(headers[0][1])['part'],'isolation')
        report=json.loads((self.artifacts/'test-0.17.0-isolation/row.json').read_text())
        self.assertTrue(report['success'])
        self.assertEqual(report['steps'][0]['name'],'Checkout')
        self.assertEqual(report['steps'][0]['status'],'passed')

    def test_actual_part_cannot_read_a_marked_tree_from_a_previous_run(self):
        self.part_fixture()
        path=self.repo/'.github/workflows/ci.yml'
        path.write_text(path.read_text().replace('          [ "$SHARED_CONTEXT" = "$GITHUB_WORKSPACE/isolation" ]',
             '''          [ "$SHARED_CONTEXT" = "$GITHUB_WORKSPACE/isolation" ]
          for tree in "$AIR2LEAN_TEST_OLD_TREE" "$AIR2LEAN_TEST_OLD_DIFF_TREE"; do
            if cat "$tree/withheld.txt" > "$AIR2LEAN_TEST_CACHE_RECOVERY" 2>/dev/null; then exit 1; fi
            [ ! -e "$tree" ]
          done'''))
        self.commit();self.pinned=self.revision();self.capture()
        trees=[self.repo/'.lake/prior-full/arbitrary-source',
               self.repo/'tests/diff/.lake/prior-matrix/arbitrary-source']
        for tree in trees:
            tree.mkdir(parents=True)
            (tree/'.air2lean-check-tree.json').write_text('{}')
            (tree/'withheld.txt').write_bytes(b'previous unrestricted source canary')
            self.assertEqual((tree/'withheld.txt').read_bytes(),b'previous unrestricted source canary')
        facet=self.write('.lake/build/keep',b'cached facet')
        recovered=self.root/'cache-recovery'
        with patch.dict(os.environ,AIR2LEAN_TEST_OLD_TREE=str(trees[0]),
                        AIR2LEAN_TEST_OLD_DIFF_TREE=str(trees[1]),
                        AIR2LEAN_TEST_CACHE_RECOVERY=str(recovered)):
            self.run_part_interpreter()  # Real committed YAML and actual restriction/commands.
        self.assertEqual(recovered.read_bytes(),b'')
        for tree in trees:self.assertFalse(tree.exists())
        self.assertEqual(facet.read_bytes(),b'cached facet')

    def test_duplicate_part_rows_fail_before_preparation_or_workflow_execution(self):
        workflow=self.part_fixture(duplicate=True)
        with patch.object(subprocess,'Popen') as started,\
             self.assertRaisesRegex(ValueError,'duplicate CI part test/0.17.0/isolation'):
            self.run_part_interpreter(workflow)
        started.assert_not_called()

    def test_actual_part_rejects_unknown_shared_condition(self):
        workflow=self.part_fixture()
        workflow['jobs']['test']['steps'][0]['if']='${{ unsupported.context }}'
        with self.assertRaisesRegex(Exception,'unsupported term'):
            self.run_part_interpreter(workflow)

    def test_actual_part_names_unsupported_comparison_values(self):
        workflow=self.part_fixture()
        workflow['jobs']['test']['strategy']['matrix']['include'][0]['examples']=[]
        workflow['jobs']['test']['steps'][0]['if']='matrix.examples == 1'
        with self.assertRaisesRegex(ValueError,"step 'Original Git source must be unavailable': unsupported expression: matrix.examples: unsupported expression scalar of list"):
            self.run_part_interpreter(workflow)

    def test_actual_part_names_numeric_overflow_without_rendering_matrix_values(self):
        workflow=self.part_fixture()
        workflow['jobs']['test']['strategy']['matrix']['include'][0]['examples']=10**10000
        workflow['jobs']['test']['steps'][0]['if']='matrix.examples == 1'
        with self.assertRaisesRegex(ValueError,"test row 0: step 'Original Git source must be unavailable': unsupported expression: matrix.examples: number is outside the GitHub expression range"):
            self.run_part_interpreter(workflow)

    def test_actual_part_environment_literals_use_shared_scalar_conversion(self):
        workflow=self.part_fixture();job=workflow['jobs']['test'];step=job['steps'][0]
        values={'BOOL':True,'FALSE':False,'NULL':None,'NUMBER':1e20,'TEXT':'K東京'}
        job['env']={'JOB_'+key:value for key,value in values.items()}
        step['env'].update({'STEP_'+key:value for key,value in values.items()})
        assertions=[]
        for prefix in ('JOB_','STEP_'):
            for key,expected in (('BOOL','true'),('FALSE','false'),('NULL',''),
                                 ('NUMBER','1E+20'),('TEXT','K東京')):
                assertions.append('[ "$'+prefix+key+'" = "'+expected+'" ]')
        step['run']='\n'.join(assertions)+'\n'+step['run']
        _executed,recovery=self.run_part_interpreter(workflow)
        self.assertTrue(recovery.exists())

    def test_actual_part_selects_only_supported_scalar_conditions(self):
        workflow=self.part_fixture();job=workflow['jobs']['test'];template=job['steps'][0]
        job['strategy']['matrix']['include'][0]['examples']=2**53+1
        cases=(('true == true',True),('false == false',True),('true != false',True),
               ('null == null',True),('null != null',False),('1 == 1.0',True),('1 == 2',False),
               ('matrix.examples == 9007199254740992',True),
               ('matrix.examples != 9007199254740994',True),
               ("'1' == 1",True),("1 == '1'",True),("'2' == 1",False),
               ("'' == 0",True),("0 == '   '",True),
               ("'9007199254740993' == matrix.examples",True),("'0x10' == '0x10'",True),
               ("'LINUX' == runner.os",True),("'NaN' == 'nan'",True),
               ("matrix.PART == 'isolation'",True),('matrix.missing == null',True))
        job['steps']=[dict(template,name='Subset case '+str(index),**{'if':condition},
                           run='printf "%s\\n" '+str(index)+' >> "$AIR2LEAN_TEST_SELECTION"\n'+template['run'])
                      for index,(condition,_expected) in enumerate(cases)]
        selection=self.root/'selected-steps'
        with patch.dict(os.environ,AIR2LEAN_TEST_SELECTION=str(selection)):
            self.run_part_interpreter(workflow)
        self.assertEqual(selection.read_text().splitlines(),
                         [str(index) for index,(_condition,expected) in enumerate(cases) if expected])

    def test_actual_part_names_unsupported_scalar_conditions_before_execution(self):
        cases=(("'0x10' == 16",''),("'0o10' == 8",''),("'1_0' == 10",''),
               ("'1e2' == 100",''),("'Infinity' == 1",''),("'NaN' == 1",''),
               ("'ordinary' == 1",''),('null == 0',''),('false == 0',''),
               ("'K' == 'k'",''),('matrix.1',''),('matrix..examples',''),
               ('matrix.examples.value',{'value':False}),('matrix.examples',float('nan')),
               ('matrix.examples',float('inf')),('matrix.examples',float('-inf')))
        for condition,value in cases:
            with self.subTest(condition=condition,value=value):
                fixture=Capture();fixture.setUp()
                try:
                    workflow=fixture.part_fixture()
                    workflow['jobs']['test']['strategy']['matrix']['include'][0]['examples']=value
                    workflow['jobs']['test']['steps'][0].update({'if':condition,'run':'exit 99'})
                    with self.assertRaises(ValueError) as caught:
                        fixture.run_part_interpreter(workflow)
                    self.assertIn(".github/workflows/ci.yml: test row 0: step 'Original Git source must be unavailable': unsupported expression:",
                                  str(caught.exception))
                finally:
                    fixture.doCleanups()

    def test_actual_part_real_yaml_data_drives_conditions_and_environment(self):
        self.part_fixture()
        target=self.repo/'.github/workflows/ci.yml'
        text=target.read_text().replace('            examples: ""','            examples: 0.0').replace(
            '            full: false','            full: FALSE').replace(
            '            mutate: false','            mutate: null').replace(
            "matrix.part == 'isolation' && runner.os == 'Linux'",
            '!matrix.examples && !matrix.full && !matrix.mutate').replace(
            '        env:\n','''        env:
          ZERO: 0.0
          NEGATIVEZERO: -0
          DISABLED: FALSE
          ABSENT: null
          UNICODE: １
          PADDED: \u00a00.0\u00a0
''',1).replace('          [ "$SHARED_CONTEXT" = "$GITHUB_WORKSPACE/isolation" ]','''          [ "$SHARED_CONTEXT" = "$GITHUB_WORKSPACE/isolation" ]
          [ "$ZERO" = 0 ]
          [ "$NEGATIVEZERO" = 0 ]
          [ "$DISABLED" = false ]
          [ "$ABSENT" = "" ]
          [ "$UNICODE" = １ ]
          [ "$PADDED" = "\u00a00.0\u00a0" ]''')+'''      - name: Disabled by real DATA
        if: matrix.full
        run: exit 99
'''
        self.write('.github/workflows/ci.yml',text.encode());self.commit();self.pinned=self.revision()
        self.capture()
        executed,recovery=self.run_part_interpreter()
        self.assertTrue(recovery.exists())
        self.assertFalse(any('exit 99' in str(command) for command in executed))

    def test_actual_literal_block_content_spaces_keep_gate_failure(self):
        self.part_fixture();path=self.repo/'.github/workflows/ci.yml'
        text=path.read_text().replace('        run: |\n',"        run: |-\n          test \"$(cat <<'SPACE_END'\n"+
                                     ' '*12+"\n          SPACE_END\n          )\" = \"\"\n",1)
        self.write('.github/workflows/ci.yml',text.encode());self.commit();self.pinned=self.revision()
        self.capture()
        with self.assertRaisesRegex(ValueError,'workflow steps failed'):self.run_part_interpreter()
        report=json.loads((self.artifacts/'test-0.17.0-isolation/row.json').read_text())
        self.assertFalse(report['success']);self.assertEqual(report['steps'][0]['status'],'failed')
        self.assertRegex(report['steps'][0]['error'],r'returned non-zero exit status 1\.$')

    def test_actual_literal_eof_data_keeps_failing_gate(self):
        self.part_fixture();text=(self.repo/'.github/workflows/ci.yml').read_text()
        start=text.index('    strategy:');steps=text.index('    steps:')
        strategy=text[start:steps].replace('            examples: ""\n','')
        code=text[steps:].replace("matrix.part == 'isolation' && runner.os == 'Linux'","matrix.examples == 'on'").replace(
            '        run: |\n','        run: |\n          exit 73\n',1)
        text=text[:start]+code+strategy+'            examples: |\n              on'
        self.write('.github/workflows/ci.yml',text.encode());self.commit();self.pinned=self.revision()
        self.capture()
        with self.assertRaisesRegex(ValueError,'workflow steps failed'):self.run_part_interpreter()
        report=json.loads((self.artifacts/'test-0.17.0-isolation/row.json').read_text())
        self.assertFalse(report['success']);self.assertEqual(report['steps'][0]['status'],'failed')
        self.assertRegex(report['steps'][0]['error'],r'returned non-zero exit status 73\.$')

    def test_actual_local_plain_trailing_colon_is_refused_before_execution(self):
        self.part_fixture();original=(self.repo/'.github/workflows/ci.yml').read_text()
        for suffix in (':',': # note'):
            text=original.replace('name: Original Git source must be unavailable',
                                  'name: Original Git source must be unavailable'+suffix)
            self.write('.github/workflows/ci.yml',text.encode())
            with self.assertRaisesRegex(ValueError,r'ci.yml:[0-9]+: unsupported YAML syntax'):
                self.run_part_interpreter()

    def test_actual_raw_unicode_break_is_refused_before_local_gate_selection(self):
        self.part_fixture();text=(self.repo/'.github/workflows/ci.yml').read_text()
        for separator in ('\u2028','\u2029'):
            self.write('.github/workflows/ci.yml',text.replace('full: false','full: false'+separator).encode())
            with self.subTest(separator=separator),self.assertRaisesRegex(ValueError,r'ci.yml:[0-9]+: unsupported raw YAML Unicode line break'):
                self.run_part_interpreter()

    def test_actual_local_refuses_extra_matrix_axes_at_shared_boundary(self):
        self.part_fixture();path=self.repo/'.github/workflows/ci.yml'
        text=path.read_text().replace('      include:','      flag: [true]\n      include:')
        self.assertIn('flag: [true]',text)
        self.write('.github/workflows/ci.yml',text.encode())
        with self.assertRaisesRegex(ValueError,'ci.yml: job test: only strategy.matrix.include is supported'):
            self.run_part_interpreter()

    def test_actual_part_real_yaml_unsupported_data_is_named_before_execution(self):
        self.part_fixture();original=(self.repo/'.github/workflows/ci.yml').read_text()
        for source in ('0x10','0o10','1e2','.inf','.NaN','!!str false','&anchor false'):
            with self.subTest(source=source):
                self.write('.github/workflows/ci.yml',original.replace('examples: ""','examples: '+source).encode())
                with self.assertRaisesRegex(ValueError,r'ci.yml:[0-9]+: unsupported'):
                    self.run_part_interpreter()
        text=original.replace('examples: ""','examples: １').replace(
            "matrix.part == 'isolation' && runner.os == 'Linux'",'matrix.examples == 1')
        self.write('.github/workflows/ci.yml',text.encode());self.commit();self.pinned=self.revision()
        self.capture()
        with self.assertRaises(ValueError) as caught:self.run_part_interpreter()
        self.assertIn("step 'Original Git source must be unavailable': unsupported expression:",str(caught.exception))
        self.assertIn("unsupported numeric string '１'",str(caught.exception))

    def test_actual_part_names_nonfinite_environment_values(self):
        for scope in ('job','step'):
            for value in (float('nan'),float('inf'),float('-inf')):
                with self.subTest(scope=scope,value=value):
                    fixture=Capture();fixture.setUp()
                    try:
                        workflow=fixture.part_fixture();job=workflow['jobs']['test']
                        target=job if scope=='job' else job['steps'][0]
                        target['env']={'FLAG':value}
                        with self.assertRaises(ValueError) as caught:
                            fixture.run_part_interpreter(workflow)
                        message=str(caught.exception)
                        self.assertIn('.github/workflows/ci.yml: test row 0:',message)
                        self.assertIn('job environment:' if scope=='job' else "step 'Original Git source must be unavailable':",message)
                        self.assertIn('unsupported non-finite numeric value',message)
                    finally:
                        fixture.doCleanups()

    def test_actual_part_names_unsupported_job_environment_values(self):
        workflow=self.part_fixture();workflow['jobs']['test']['env']={'FLAG':[]}
        with self.assertRaisesRegex(ValueError,'test row 0: job environment: unsupported expression: unsupported expression scalar of list'):
            self.run_part_interpreter(workflow)

    def test_actual_part_names_unsupported_step_environment_values(self):
        workflow=self.part_fixture()
        workflow['jobs']['test']['steps'][0]['env']['FLAG']={}
        with self.assertRaisesRegex(ValueError,"step 'Original Git source must be unavailable': unsupported expression: unsupported expression scalar of dict"):
            self.run_part_interpreter(workflow)

    @unittest.skipUnless(sys.platform=='darwin' and os.uname().machine=='arm64',
                         'actual host dispatch requires Apple silicon macOS')
    def test_actual_host_wrapper_runs_unrestricted_discovery_and_rejects_part(self):
        import signal

        self.part_fixture()
        for name in ('local-ci.sh','local-ci-steps.py','zig-default.sh'):
            self.write('scripts/'+name,(ROOT/'scripts'/name).read_bytes())
        for name in ('Dockerfile.local-ci','lake-manifest.json','tests/diff/lean-toolchain',
                     'tests/diff/lake-manifest.json'):
            self.write(name,(ROOT/name).read_bytes())
        self.write('README.md',b'caller source remains reachable\n')
        self.write('.github/workflows/ci.yml',b'''jobs:
  macos:
    runs-on: macos-14
    strategy:
      matrix:
        include:
          - zig: 0.17.0
    steps:
      - name: Actual unrestricted host probe
        run: |
          uname -s > "$RUNNER_TEMP/system"
          uname -m > "$RUNNER_TEMP/machine"
          git -C ../../../.. show HEAD:README.md > "$RUNNER_TEMP/caller-readme"
''')
        self.write('.github/ci-inputs.json',json.dumps({'schema':'air2lean-ci-inputs/2',
            'parts':{'macos/0.17.0':{'inputs':['scripts/**','.github/**']}}}).encode())
        self.commit();self.pinned=self.revision()
        home=self.root/'host-home';home.mkdir()
        results=self.repo/'.lake/local-ci-results'
        environment=dict(os.environ,HOME=str(home),AIR2LEAN_LOCAL_RESULTS=str(results),
                         AIR2LEAN_LOCAL_TIMEOUT='30s')
        for mode in ('discover','part'):
            with self.subTest(mode=mode):
                previous=set(results.glob('run.*'))
                with subprocess.Popen(['bash',str(self.repo/'scripts/local-ci.sh'),mode,'macos/0.17.0'],
                                      env=environment,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                                      start_new_session=True) as result:
                    try:
                        _stdout,stderr=result.communicate(timeout=40)
                    finally:
                        if result.returncode is None:
                            runner.stop_group(result,signal.SIGTERM)
                added=set(results.glob('run.*'))-previous
                self.assertEqual(len(added),1)
                artifacts=added.pop();row=artifacts/'macos-0.17.0'
                report=json.loads((row/'row.json').read_text())
                self.assertFalse(report['restriction']['qualified'])
                self.assertFalse(report['restriction']['files_withheld'])
                self.assertEqual(report['restriction']['gap'],runner.HOST_SOURCE_GAP)
                if mode=='discover':
                    self.assertEqual(result.returncode,0,stderr.decode(errors='replace'))
                    self.assertTrue(report['success'])
                    self.assertEqual((row/'system').read_text(),'Darwin\n')
                    self.assertEqual((row/'machine').read_text(),'arm64\n')
                    self.assertEqual((row/'caller-readme').read_bytes(),b'caller source remains reachable\n')
                else:
                    self.assertNotEqual(result.returncode,0)
                    self.assertFalse(report['success'])
                    self.assertTrue(report['restriction']['requested'])
                    self.assertIn('restricted host qualification is unavailable',report['error'])
                    self.assertFalse((row/'system').exists())

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

    def test_actual_inside_bootstrap_checks_archive_before_extracting(self):
        self.capture()
        binary=self.root/'inside-bin';binary.mkdir()
        (binary/'flock').write_text('#!/bin/sh\nexit 0\n')
        checksum=shutil.which('sha256sum') or shutil.which('gsha256sum')
        if checksum:
            (binary/'sha256sum').write_text('#!/bin/sh\nexec '+shlex.quote(checksum)+' "$@"\n')
        else:
            checksum=shutil.which('shasum');self.assertIsNotNone(checksum)
            (binary/'sha256sum').write_text('#!/bin/sh\nexec '+shlex.quote(checksum)+' -a256 "$@"\n')
        extracted=self.root/'tar-called'
        (binary/'tar').write_text('#!/bin/sh\nprintf extracted > "$AIR2LEAN_TEST_EXTRACTED"\nexit 77\n')
        for path in binary.iterdir():path.chmod(0o755)
        script=(ROOT/'scripts/local-ci.sh').read_text()
        for old,new in (('/snapshot',self.snapshot),('/work',self.repo),
                        ('/cache',self.root/'cache'),('/artifacts',self.artifacts)):
            script=script.replace(old,str(new))
        (self.root/'cache').mkdir()
        launcher=self.root/'inside-bootstrap.sh';launcher.write_text(script)
        environment=dict(os.environ,PATH=str(binary)+os.pathsep+os.environ['PATH'],
                         AIR2LEAN_TEST_EXTRACTED=str(extracted))
        command=['bash',str(launcher),'--inside','part','test/0.17.0/lean','']
        valid=subprocess.run(command,env=environment,capture_output=True)
        self.assertEqual(valid.returncode,77,valid.stderr.decode(errors='replace'))
        self.assertEqual(extracted.read_text(),'extracted');extracted.unlink()
        with (self.snapshot/'source.tar').open('ab') as archive:archive.write(b'changed after capture')
        invalid=subprocess.run(command,env=environment,capture_output=True)
        self.assertNotEqual(invalid.returncode,0)
        self.assertNotEqual(invalid.returncode,77)
        self.assertFalse(extracted.exists())
        self.assertIn(b'checksum',invalid.stderr)

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


class FixtureConsumers(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec=importlib.util.spec_from_file_location('local_fixture_checks',ROOT/'scripts/fixture-checks.py')
        cls.fixture=importlib.util.module_from_spec(spec);spec.loader.exec_module(cls.fixture)

    def units(self, text):
        temp=tempfile.TemporaryDirectory();self.addCleanup(temp.cleanup)
        root=Path(temp.name);path=root/'.github/workflows/ci.yml';path.parent.mkdir(parents=True)
        path.write_text(text)
        with patch.object(self.fixture,'ROOT',root),patch.object(self.fixture,'is_proof_fixture',return_value=True):
            return self.fixture.discover(SimpleNamespace())

    WORKFLOW='''jobs:
  test:
    runs-on: ubuntu-24.04
    env:
      FLAG: VALUE
    steps:
      - name: fixture
        run: tests/example/check.sh
'''

    def discover(self, value):
        units=self.units(self.WORKFLOW.replace('VALUE',value))
        self.assertEqual(len(units),1)
        return units[0]

    def test_real_fixture_job_and_step_conditions_refuse_unsupported_typed_data(self):
        for scope,anchor,indent in (('job test','    runs-on:','    '),
                                    ('test: fixture','        run:','        ')):
            for source in ('[true]','0.0','0'):
                text=self.WORKFLOW.replace('VALUE','null').replace(anchor,indent+'if: '+source+'\n'+anchor)
                with self.subTest(scope=scope,source=source),self.assertRaisesRegex(self.fixture.Unsupported,
                        'ci.yml: '+scope+': unsupported condition DATA:'):
                    self.units(text)
            for source,count in (('FALSE',0),('null',1),('needs.other.outputs.value',1),('failure()',0)):
                text=self.WORKFLOW.replace('VALUE','null').replace(anchor,indent+'if: '+source+'\n'+anchor)
                with self.subTest(scope=scope,source=source):
                    units=self.units(text)
                    self.assertEqual(len(units),count)
                    self.assertTrue(all(unit['error'] is None for unit in units))

    def test_real_fixture_run_scalars_are_formatted_before_check_discovery(self):
        for source in ('false','null','0.0'):
            text=self.WORKFLOW.replace('VALUE','null').replace('tests/example/check.sh',source)
            with self.subTest(source=source):
                self.assertEqual(self.units(text),[])
        text=self.WORKFLOW.replace('VALUE','null').replace('tests/example/check.sh','[unsupported]')
        with self.assertRaisesRegex(self.fixture.Unsupported,
                                   'ci.yml: test: fixture: unsupported expression scalar of list'):
            self.units(text)

    def test_actual_discover_formats_real_yaml_environment_scalars(self):
        for source,expected in (('null',''),('false','false'),('true','true'),
                                ('0','0'),('1.5','1.5'),("'雪'",'雪')):
            with self.subTest(source=source):
                unit=self.discover(source)
                self.assertEqual(unit['env'],{'FLAG':expected})
                self.assertIsNone(unit['error'])

    def test_actual_discover_names_unsupported_environment_data(self):
        unit=self.discover('[unsupported]')
        self.assertIn('unsupported expression scalar of list',unit['error'])
        self.assertIn('.github/workflows/ci.yml: test: fixture',unit['error'])
        self.assertEqual(unit['name'],'test: fixture')
        self.assertEqual(unit['env'],{})
        self.assertEqual(unit['toolchains'],{'patched':[],'stock':[]})
        command,env=self.fixture.stage(unit,Path('unused'))
        failed=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        self.assertEqual(failed.returncode,1)
        self.assertIn('test: fixture',failed.stderr)
        for value in ([],{},float('inf')):
            with self.subTest(value=repr(value)),self.assertRaises(self.fixture.Unsupported):
                self.fixture.render(value,{})

    def test_renderer_retains_context_placeholders_and_unicode_interpolation(self):
        self.assertEqual(self.fixture.render('${{ github.workspace }}/${{ runner.temp }}/${{ matrix.value }}',
                                             {'value':'雪'}),'@WORKSPACE@/@RUNNER_TEMP@/雪')
        self.assertIs(self.fixture.CR.canonical,self.fixture.TM.canonical)
        self.assertEqual(self.fixture.CR.canonical({'z':0.0,'a':False}),'{"a":false,"z":0.0}')


if __name__=='__main__':unittest.main()
