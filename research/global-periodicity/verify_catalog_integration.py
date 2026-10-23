"""Check catalog registration and the public headlines on the upstream base.

The separate separation runners replay every generated certificate module in
both environments. This additional check verifies integration of the six
public modules into the standalone core catalog.
"""
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import argparse

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('verify', HERE/'verify_trace_separation.py')
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)
PREFIX = 'Ruliology.CellularAutomata.'
TARGETS = {
    'Rule30TraceEdgeResearch': 'problem1_of_edgeObservable',
    'Rule30TraceRigidityResearch': 'no_left_recovery_from_eventual_finiteness',
    'Rule30TraceAmbiguityResearch': 'arbitrarily_long_finite_left_ambiguity',
    'Rule30TraceSeparationResearch': 'separate_minus_one_minus_two',
    'Rule30TraceSeparationThreeResearch': 'separate_minus_two_minus_three',
    'Rule30ColumnSeparationResearch': 'columns_distinguishable',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    evidence = HERE/'integration-evidence'
    evidence.mkdir(exist_ok=True)
    root = (PROJECT/'lean/Ruliology.lean').read_text(encoding='utf-8')
    for name in TARGETS:
        assert 'public import '+PREFIX+name in root, name
    checker = PROJECT/'Check.lean'
    original = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=PROJECT)
    assert checker.read_bytes() == original, 'Official checker was modified'
    verify.execute([args.lake, 'build', 'Ruliology'], PROJECT/'lean', evidence/'core-build.log')
    modules = []
    with ThreadPoolExecutor(max_workers=2) as executor:
        jobs = [executor.submit(verify.verify_module, args.lake, PROJECT, evidence,
                                PREFIX+n, PREFIX+n+'.'+h) for n,h in TARGETS.items()]
        for job in as_completed(jobs):
            modules.append(job.result())
    sources = [PROJECT/'lean/Ruliology.lean', checker]
    sources += [PROJECT/'lean/Ruliology/CellularAutomata'/(n+'.lean') for n in TARGETS]
    sources += list((PROJECT/'lean/Ruliology/CellularAutomata/Rule30Certificates').glob('TraceSepH15*.lean'))
    report = {'verdict': 'pass', 'standalone_core_catalog_build': True,
              'base_commit': subprocess.check_output(['git','rev-parse','HEAD'], cwd=PROJECT, text=True).strip(),
              'checker_unchanged': True, 'full_problem_claim': False,
              'edge_observable_proved': False, 'modules': modules,
              'source_sha256': {p.relative_to(PROJECT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in sources}}
    (HERE/'catalog-integration-verification.json').write_text(
        json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'verdict': 'pass', 'public_modules': len(modules)}))


if __name__ == '__main__':
    main()
