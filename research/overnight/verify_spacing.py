"""Replay the reconstruction identity and exact iteration obstruction."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REL = Path('lean/Ruliology/CellularAutomata/Rule30SpacingRenormalizationResearch.lean')
MODULE = 'Ruliology.CellularAutomata.Rule30SpacingRenormalizationResearch'
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
    evidence = HERE / 'spacing-evidence' / tag
    evidence.mkdir(parents=True, exist_ok=True)
    (evidence / 'report.json').write_text('{"verdict":"running"}\n', encoding='utf-8')
    source = (ROOT / REL).read_text(encoding='utf-8')
    if tag == 'pinned':
        adapted = source.removeprefix('module\n').replace('public import ', 'import ')
        adapted = adapted.replace('@[expose] public section', '')
        target = project / REL
        if target.exists() and target.read_text(encoding='utf-8') != adapted:
            raise RuntimeError('Different source in pinned worktree')
        target.write_text(adapted, encoding='utf-8', newline='\n')
    expected = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project / 'Check.lean').read_bytes().replace(b'\r\n', b'\n') == expected
    audit.run([args.lake, 'build', MODULE], project, evidence / 'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', MODULE, '--claim', 'partial']
    for h in ['reconstruction_translate', 'support_transfer', 'finite_transfer', 'transform_spaced_iff',
              'periodFive_spaced', 'transform_not_spaced', 'second_translation_fails']:
        argv.extend(['--headline', MODULE + '.' + h])
    log = evidence / 'check.log'
    audit.run(argv, project, log)
    data = json.loads([l for l in log.read_text(encoding='utf-8').splitlines()
                       if l.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    report = {'verdict': 'pass', 'full_problem_claim': False, 'period_two_excluded': False,
              'spacing_preserved_generally': False, 'unbounded_reconstruction_identity': True,
              'checker_modified': False, 'proof_bodies_unchanged': True,
              'source_sha256': hashlib.sha256((project / REL).read_bytes()).hexdigest(),
              'project_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project,
                                                       text=True).strip(), 'check': data}
    (evidence / 'report.json').write_text(json.dumps(report, indent=2) + '\n',
                                        encoding='utf-8', newline='\n')
    print(json.dumps({'verdict': report['verdict'], 'environment': tag,
                      'constants': data['replay']['constants'],
                      'headlines': len(data['headlines'])}))


if __name__ == '__main__':
    main()
