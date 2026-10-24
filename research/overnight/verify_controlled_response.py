"""Full-kernel replay of controlled-response identities; no full prize claim."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import audit_contributions as audit


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lake', required=True)
    ap.add_argument('--project', type=Path, default=audit.ROOT)
    ap.add_argument('--refresh-generated', action='store_true',
                    help='Refresh only an audit copy matching the previous successful source hash')
    args = ap.parse_args()
    project = args.project.resolve()
    module = audit.PREFIX+'Rule30ControlledResponseResearch'
    rel = Path('lean')/Path(module.replace('.', '/')).with_suffix('.lean')
    source = (audit.ROOT/rel).read_text(encoding='utf-8')
    tag = 'catalog' if project == audit.ROOT else 'pinned'
    if tag == 'pinned':
        source = source.removeprefix('module\n').replace('public import ', 'import ').replace('@[expose] public section', '')
        target = project/rel
        if target.exists() and target.read_text(encoding='utf-8') != source:
            previous_path = audit.HERE/'controlled-response-evidence'/tag/'report.json'
            if not args.refresh_generated or not previous_path.exists():
                raise RuntimeError('Refusing to overwrite different proof source')
            previous = json.loads(previous_path.read_text(encoding='utf-8'))
            if hashlib.sha256(target.read_bytes()).hexdigest() != previous['source_sha256']:
                raise RuntimeError('Audit copy does not match its previous verified hash')
        target.write_text(source, encoding='utf-8', newline='\n')
    checked_bytes = (project/rel).read_bytes()
    expected = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == expected
    evidence = audit.HERE/'controlled-response-evidence'/tag
    evidence.mkdir(parents=True, exist_ok=True)
    audit.run([args.lake, 'build', module], project, evidence/'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
    for name in ['run_sound', 'responseEq_iff_runs', 'responseEq_all_prepend',
                 'responseEq_two', 'sameResponse_iff_diagonal', 'sameResponse_iff_drv',
                 'tail_011_drv', 'tail_101_drv', 'responseEq_iff_observationPrefix',
                 'short_window_agreement', 'short_window_not_sameResponse',
                 'fixed_driver_counterexample', 'feedback_left_equal',
                 'tail_011_center', 'tail_101_center']:
        argv += ['--headline', module+'.'+name]
    log = evidence/'check.log'
    audit.run(argv, project, log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    assert (project/rel).read_bytes() == checked_bytes, 'Proof source changed during verification'
    report = {'verdict': 'pass', 'scope': 'unbounded controlled response equivalence and terminal rewrite soundness',
        'normal_form_completeness_proved': False, 'fixed_driver_classification_proved': False,
        'full_problem_claim': False, 'checker_modified': False,
        'source_sha256': hashlib.sha256(checked_bytes).hexdigest(),
        'project_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip(),
        'check': data}
    (evidence/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'environment': tag, 'verdict': 'pass', 'constants': data['replay']['constants']}))


if __name__ == '__main__':
    main()
