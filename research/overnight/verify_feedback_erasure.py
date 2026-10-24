"""Fully replay finite feedback erasure against unchanged working/pinned checkers."""
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
    args = ap.parse_args()
    project = args.project.resolve()
    tag = 'catalog' if project == audit.ROOT else 'pinned'
    module = audit.PREFIX+'Rule30FeedbackErasureResearch'
    rel = Path('lean')/Path(module.replace('.', '/')).with_suffix('.lean')
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
    evidence = audit.HERE/'feedback-erasure-evidence'/tag
    evidence.mkdir(parents=True, exist_ok=True)
    audit.run([args.lake, 'build', module], project, evidence/'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
    for h in ['white_step_erases_distinction','initial_responses_differ','same_left_forever',
              'single_finite','double_finite','configurations_differ','same_actual_left',
              'same_actual_center','same_actual_right_head','initial_rights_not_sameResponse',
              'center_not_eventually_constant','right_head_not_eventually_constant',
              'finite_feedback_counterexample']:
        argv += ['--headline', module+'.'+h]
    log = evidence/'check.log'
    audit.run(argv, project, log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    assert (project/rel).read_bytes() == checked
    report = {'verdict': 'pass', 'checker_modified': False, 'full_problem_claim': False,
        'scope': 'finite actual feedback erasure with non-eventually-constant common traces',
        'different_left_edges': False, 'novelty_claim': False,
        'source_sha256': hashlib.sha256(checked).hexdigest(),
        'project_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip(),
        'check': data}
    (evidence/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'environment': tag, 'verdict': 'pass', 'constants': data['replay']['constants']}))


if __name__ == '__main__':
    main()
