#!/usr/bin/env python3
"""Serial kernel mutants, after baseline elaboration. Never edits library files."""
from pathlib import Path
import importlib.util
import re
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[3]
# Share the strict located-diagnostic classifier with the existing bitops gate.
_spec = importlib.util.spec_from_file_location(
    "bitops_mutant_classifier", ROOT / "tests/roadmap/bitops/classify_mutant.py")
_classifier = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_classifier)
is_semantic_rejection = _classifier.is_semantic_rejection
MUTANTS = {
    'omit-extra-byte': ('a.create (n.toNat + 1) 1', 'a.create n.toNat 1'),
    'wrong-sentinel-offset': ('store 1 (p.add n.toNat) sentinel', 'store 1 p sentinel'),
}
MUTANT_PROOF = 'by\n  with_unfolding_all\n    conv =>\n      lhs\n      reduce\n  all_goals decide +kernel'
def runtime_definition(source):
    start = source.index('def Allocator.allocSentinel ')
    end = source.index('/-- `free(s)`', start)
    return source[start:end].replace('Allocator.allocSentinel', 'Allocator.mutantSentinel', 1)
def mutated(source, name):
    before, after = MUTANTS[name]
    if source.count(before) != 1:
        raise ValueError(f'{name}: expected exactly one mutation anchor')
    return source.replace(before, after, 1)
def mutant_fixture(baseline, definition, name):
    checks = baseline.replace('Allocator.allocSentinel', 'Allocator.mutantSentinel')
    # Kernel decide diagnoses a failed proof lazily outside a transparency
    # wrapper. Normalize the observation definitionally before deciding, so its
    # false diagnostic cannot get stuck behind private fixture definitions.
    # Conversion and the final proof are kernel checked; every claim stays intact.
    checks = re.sub(r'\bby decide(?: \+kernel)?(?=\n|$)',
        MUTANT_PROOF, checks)
    return checks.replace('open Zig',
        'namespace Zig\n' + mutated(definition, name) + '\nend Zig\nopen Zig', 1)
def main():
    baseline = ROOT / 'tests/roadmap/byte-sentinel/Check.lean'
    subprocess.run(['lake', 'env', 'lean', str(baseline)], cwd=ROOT, check=True)
    definition = runtime_definition((ROOT / 'ZigLean/Mem/Alloc.lean').read_text())
    checks = baseline.read_text()
    with tempfile.TemporaryDirectory(prefix='byte-sentinel-mutants-') as temp:
        for name in MUTANTS:
            source = mutant_fixture(checks, definition, name)
            path = Path(temp) / (name + '.lean')
            path.write_text(source)
            result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                capture_output=True, text=True)
            log = result.stdout + result.stderr
            # Baseline compiled first. Only an explicit false kernel decide result counts;
            # parse/import/resource errors are never classified as mutation detection.
            if not is_semantic_rejection(result.returncode, log):
                raise RuntimeError(f'{name}: not an exclusive semantic decide refutation:\n{log}')
            print(f'{name}: killed by false kernel proposition')
if __name__ == '__main__':
    main()
