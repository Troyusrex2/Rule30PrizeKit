"""Replay the right-edge coordinate identity and its generic countermodel."""
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
    module = audit.PREFIX+'Rule30MovingFrameBarrierResearch'
    rel = Path('lean/Ruliology/CellularAutomata/Rule30MovingFrameBarrierResearch.lean')
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
    evidence = audit.HERE/'moving-frame-evidence'/tag
    evidence.mkdir(parents=True, exist_ok=True)
    audit.run([args.lake, 'build', module], project, evidence/'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
    for h in ['rows_sound', 'center_is_diagonal', 'counterBit_exact_period',
              'counterBit_periods_unbounded', 'counterDiagonal_eventuallyPeriodic',
              'oddCounterBit_exact_period', 'oddCounterBit_eventual_period_lower_bound',
              'oddCounterDiagonal_white', 'countermodel']:
        argv += ['--headline', module+'.'+h]
    log = evidence/'check.log'
    audit.run(argv, project, log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    assert (project/rel).read_bytes() == checked
    report = {'verdict': 'pass',
        'scope': 'known coordinate reencoding and a generic countermodel to a period-only inference',
        'source_sha256': hashlib.sha256(checked).hexdigest(), 'checker_modified': False,
        'Rule30_center_nonperiodicity_proved': False, 'new_temporal_period_excluded': False,
        'full_problem_claim': False, 'novelty_claim': False,
        'reference_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip(),
        'check': data}
    (evidence/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'environment': tag, 'verdict': 'pass', 'constants': data['replay']['constants']}))


if __name__ == '__main__':
    main()
