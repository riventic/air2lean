#!/usr/bin/env python3
"""Run a precompiled native fixture in an isolated directory, with a short timeout."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[3]
SPEC=importlib.util.spec_from_file_location('diff_report',ROOT/'scripts/diff-report.py')
REPORT=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REPORT)

def verify(root):
    directory=root/'tests/diff/out/zig/outcome-accounting'
    def rows(name):return [REPORT.decode(line) for line in REPORT.lines(directory/name)]
    if rows('prefix.jsonl') != [{'ok':7}]:raise AssertionError('valid prefix output lost')
    metadata=rows('prefix.jsonl.outcomes')
    if len(metadata)!=2:raise AssertionError('valid metadata prefix or failure row lost')
    REPORT.observation(json.dumps(metadata[0]),{'ok':7},'native')
    if metadata[0]['kind']!='value' or metadata[1]!={'schema':1,'kind':'input_failure'}:
        raise AssertionError('metadata order or failure category changed')
    observed=REPORT.failure_observations(root,['outcome-accounting'])
    if len(observed)!=1 or observed[0]['input_index']!=2:raise AssertionError('failure index changed')
    render=rows('renderer.jsonl')
    if render!=[{'fail':'harnessRenderFailure'}]:raise AssertionError('renderer failure lost')
    kind,_=REPORT.observation(json.dumps(rows('renderer.jsonl.outcomes')[0]),render[0],'native')
    status=REPORT.classify(render[0],{'fail':'Zig.Error.panic'},kind,REPORT.Kind.MODEL_PANIC,None)
    if status!=REPORT.Status.NATIVE_HARNESS_FAILURE:raise AssertionError('renderer failure became semantic mismatch')
    # Exercise the same summary mutation-eligibility path on the actual native row.
    isolated=root/'accounting'
    (isolated/'examples/outcome-accounting').mkdir(parents=True)
    inputs=isolated/'tests/diff/outcome-accounting/inputs';inputs.mkdir(parents=True)
    (inputs/'renderer.jsonl').write_text('[]\n')
    for side in ('zig','lean'):(isolated/'tests/diff/out'/side/'outcome-accounting').mkdir(parents=True)
    for suffix in ('','.outcomes'):
        target=isolated/'tests/diff/out/zig/outcome-accounting'/('renderer.jsonl'+suffix)
        target.write_bytes((directory/('renderer.jsonl'+suffix)).read_bytes())
    model=isolated/'tests/diff/out/lean/outcome-accounting/renderer.jsonl'
    model.write_text('{"fail":"Zig.Error.panic"}\n')
    Path(str(model)+'.outcomes').write_text('{"schema":1,"kind":"model_panic","legacy_line":"{\\"fail\\":\\"Zig.Error.panic\\"}"}\n')
    summary=isolated/'summary.json'
    if REPORT.compare(isolated,['outcome-accounting'],'fixture','fixture',summary)!=1:
        raise AssertionError('renderer setup failure passed gate')
    report=REPORT.read_summary(summary)
    if report['mutation_eligible']!=0 or report['setup_failures']!=1:
        raise AssertionError('renderer setup failure counted as mutation detection')
    source=rows('source.jsonl')
    if source!=[{'fail':'panic'}]:raise AssertionError('tested source panic changed')
    kind,_=REPORT.observation(json.dumps(rows('source.jsonl.outcomes')[0]),source[0],'native')
    if kind!=REPORT.Kind.NATIVE_PANIC:raise AssertionError('tested source panic became harness failure')
    for name,expected in [('signal',REPORT.Kind.NATIVE_SIGNAL),
                          ('interrupt',REPORT.Kind.NATIVE_HARNESS_FAILURE),
                          ('abort',REPORT.Kind.NATIVE_HARNESS_FAILURE),
                          ('renderer-fault',REPORT.Kind.NATIVE_HARNESS_FAILURE)]:
        legacy=rows(name+'.jsonl')
        # A synchronous fault signal is reported by name (the fixture raises SIGFPE).
        if legacy not in ([{'fail':'SIGFPE'}],[{'fail':'unknown'}]):raise AssertionError(name+' legacy failure changed')
        kind,_=REPORT.observation(json.dumps(rows(name+'.jsonl.outcomes')[0]),legacy[0],'native')
        if kind!=expected:raise AssertionError(name+' phase/signal classification changed')
        # Real harness and resource failures stay fatal even against model-illegal.
        status=REPORT.classify(legacy[0],{'fail':'Zig.Error.illegal'},kind,REPORT.Kind.ILLEGAL,None,pinned=True)
        target=REPORT.Status.ILLEGAL if name=='signal' else REPORT.Status.NATIVE_HARNESS_FAILURE
        if status!=target:raise AssertionError(name+' illegal exclusion masked a harness failure')
        status=REPORT.classify(legacy[0],{'ok':7},kind,REPORT.Kind.VALUE,None)
        target=REPORT.Status.MISMATCH if name=='signal' else REPORT.Status.NATIVE_HARNESS_FAILURE
        if status!=target:raise AssertionError(name+' valid model comparison changed')

def main():
    binary=Path(sys.argv[1]).resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix='air2lean-outcome-native-') as name:
        root=Path(name);inputs=root/'tests/diff/outcome-accounting/inputs';inputs.mkdir(parents=True)
        for fixture,text in {'prefix':'[0]\n{malformed\n','renderer':'[]\n','source':'[]\n','signal':'[]\n','interrupt':'[]\n','abort':'[]\n','renderer-fault':'[]\n'}.items():
            (inputs/(fixture+'.jsonl')).write_text(text)
        subprocess.run([str(binary)],cwd=root,check=True,timeout=5)
        verify(root)
    print('native producer phase, signal, resource interruption, renderer and source panic checks passed')

if __name__=='__main__':main()
