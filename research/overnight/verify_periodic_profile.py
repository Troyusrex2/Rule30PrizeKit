"""Replay an explicit infinite-tail counterexample to OR-only recovery."""
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
    module = audit.PREFIX+'Rule30PeriodicProfileCounterResearch'
    rel = Path('lean/Ruliology/CellularAutomata/Rule30PeriodicProfileCounterResearch.lean')
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
    evidence = audit.HERE/'periodic-profile-evidence'/tag
    evidence.mkdir(parents=True, exist_ok=True)
    audit.run([args.lake, 'build', module], project, evidence/'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
    for h in ['frame_step', 'iterate_frame', 'full_period_eight', 'same_OR',
              'OR_nonconstant', 'heads_differ', 'tail_OR_different', 'infinite_true', 'infinite_false',
              'loss_frame_step', 'loss_full_period_eight', 'loss_head_period_two',
              'loss_full_period_lower_bound', 'loss_not_head_period_one', 'loss_infinite']:
        argv += ['--headline', module+'.'+h]
    log = evidence/'check.log'
    audit.run(argv, project, log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    assert (project/rel).read_bytes() == checked
    report = {'verdict': 'pass',
        'scope': 'eight-periodic infinite-tail counterexamples to OR-only recovery and head-period detection',
        'source_sha256': hashlib.sha256(checked).hexdigest(), 'checker_modified': False,
        'finite_support_conjecture_refuted': False, 'normal_form_completeness_proved': False,
        'Rule30_center_nonperiodicity_proved': False, 'new_temporal_period_excluded': False,
        'full_problem_claim': False, 'literature_priority_claim': False,
        'reference_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip(),
        'check': data}
    (evidence/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'environment': tag, 'verdict': 'pass', 'constants': data['replay']['constants']}))


if __name__ == '__main__':
    main()
