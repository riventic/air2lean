#!/usr/bin/env python3
"""Filesystem-only cache hygiene regressions; no runner/toolchain subprocesses."""
import ast
import os
from pathlib import Path
import re
import stat
import subprocess
import tomllib
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[3]
source=ast.parse((ROOT/'scripts/local-ci-steps.py').read_text())
functions=[node for node in source.body if isinstance(node,ast.FunctionDef) and node.name in ('prune_stale_modules','prune_current_cache')]
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

if __name__=='__main__':unittest.main()
