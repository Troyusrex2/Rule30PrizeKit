"""Replay stripe-prefix restrictions and an explicitly conditional rank reduction."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import audit_contributions as audit


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project', type=Path, default=audit.ROOT)
    ap.add_argument('--lake', required=True)
    args = ap.parse_args()
    project = args.project.resolve()
    tag = 'catalog' if project == audit.ROOT else 'pinned'
    module = audit.PREFIX+'Rule30StripePrefixResearch'
    rel = Path('lean/Ruliology/CellularAutomata/Rule30StripePrefixResearch.lean')
    source = (audit.ROOT/rel).read_text(encoding='utf-8')
    if tag == 'pinned':
        source = source.removeprefix('module\n').replace('public import ', 'import ').replace('@[expose] public section', '')
        target = project/rel
        if target.exists() and target.read_text(encoding='utf-8') != source:
            raise RuntimeError('Refusing to overwrite different proof source')
        target.write_text(source, encoding='utf-8', newline='\n')
    checked = (project/rel).read_bytes()
    checker = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    evidence = audit.HERE/'stripe-prefix-evidence'/tag
    evidence.mkdir(parents=True, exist_ok=True)
    audit.run([args.lake, 'build', module], project, evidence/'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
    for h in ['first_defect_white', 'inX_first_defect_even', 'finite_first_defect',
              'finite_inX_even_first_defect_two_step', 'Q01_of_integerRanking',
              'no_eventual_period_two_of_integerRanking']:
        argv += ['--headline', module+'.'+h]
    log = evidence/'check.log'
    audit.run(argv, project, log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    assert (project/rel).read_bytes() == checked
    report = {'verdict': 'pass', 'scope': 'standard stripe-pivot consequences and conditional pathwise rank reduction',
        'source_sha256': hashlib.sha256(checked).hexdigest(), 'checker_modified': False,
        'ranking_constructed': False, 'Q01_proved': False, 'new_temporal_period_excluded': False,
        'full_problem_claim': False,
        'reference_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip(),
        'check': data}
    (evidence/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'environment': tag, 'verdict': 'pass', 'constants': data['replay']['constants']}))


if __name__ == '__main__':
    main()
