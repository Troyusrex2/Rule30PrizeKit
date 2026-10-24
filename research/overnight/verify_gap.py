"""Full replay of the packed-cone engine and spacing-three/five counterexample."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREFIX = 'Ruliology.CellularAutomata.'
TARGETS = {
    'Rule30PackedReconstructionResearch': ['packed_sound'],
    'Rule30SpacingGapCounterexampleResearch': ['gate31_gaps', 'gate31_spaced', 'seventeen_white'],
}
spec = importlib.util.spec_from_file_location('audit', HERE / 'audit_contributions.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project', type=Path, default=ROOT)
    ap.add_argument('--lake', required=True)
    args = ap.parse_args()
    project = args.project.resolve()
    tag = 'catalog' if project == ROOT else 'pinned'
    evidence = HERE / 'gap-evidence' / tag
    evidence.mkdir(parents=True, exist_ok=True)
    report = {'verdict': 'running', 'checker_modified': False, 'proof_bodies_unchanged': True,
              'full_problem_claim': False, 'finite_right_realizability_claim': False,
              'modules': []}
    target_report = evidence / 'report.json'
    target_report.write_text(json.dumps(report) + '\n', encoding='utf-8')
    expected = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project / 'Check.lean').read_bytes().replace(b'\r\n', b'\n') == expected
    for stem, headlines in TARGETS.items():
        rel = Path('lean/Ruliology/CellularAutomata') / (stem + '.lean')
        source = (ROOT / rel).read_text(encoding='utf-8')
        if tag == 'pinned':
            source = source.removeprefix('module\n').replace('public import ', 'import ')
            source = source.replace('@[expose] public section', '')
            target = project / rel
            if target.exists() and target.read_text(encoding='utf-8') != source:
                raise RuntimeError('Different pinned source: ' + stem)
            target.write_text(source, encoding='utf-8', newline='\n')
        module = PREFIX + stem
        audit.run([args.lake, 'build', module], project, evidence / (stem + '.build.log'))
        argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
        for h in headlines:
            argv.extend(['--headline', module + '.' + h])
        log = evidence / (stem + '.check.log')
        audit.run(argv, project, log)
        data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines()
                           if s.startswith('{')][-1])
        assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
        assert all(h['ok'] for h in data['headlines'])
        report['modules'].append({'module': module,
                                 'source_sha256': hashlib.sha256((project / rel).read_bytes()).hexdigest(),
                                 'check': data})
        target_report.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
        print(json.dumps({'environment': tag, 'module': module,
                          'constants': data['replay']['constants'], 'verdict': 'pass'}), flush=True)
    report['verdict'] = 'pass'
    report['project_commit'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project,
                                                       text=True).strip()
    target_report.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
