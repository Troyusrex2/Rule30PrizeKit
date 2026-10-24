"""Replay the exact return criterion, retaining only hash-matched verified dependencies."""
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
    retained = []
    for folder in ['spacing-evidence', 'driven-wall-evidence']:
        path = audit.HERE/folder/tag/'report.json'
        prior = json.loads(path.read_text(encoding='utf-8'))
        assert prior['verdict'] == 'pass' and not prior['checker_modified']
        modules = prior.get('modules', [{'module': audit.PREFIX+'Rule30SpacingRenormalizationResearch',
            'source_sha256': prior.get('source_sha256'), 'check': prior.get('check')}])
        for record in modules:
            module = record['module']
            rel = Path('lean')/Path(module.replace('.', '/')).with_suffix('.lean')
            source = (project/rel).read_bytes()
            assert hashlib.sha256(source).hexdigest() == record['source_sha256']
            expected = (audit.ROOT/rel).read_text(encoding='utf-8')
            if tag == 'pinned':
                expected = expected.removeprefix('module\n').replace('public import ', 'import ').replace('@[expose] public section', '')
            assert (project/rel).read_text(encoding='utf-8') == expected
            data = record['check']
            assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
            assert all(h['ok'] for h in data['headlines'])
            retained.append({'module': module, 'source_sha256': record['source_sha256'],
                'previous_full_replay_constants': data['replay']['constants'],
                'previous_report': path.relative_to(audit.ROOT).as_posix(), 'source_hash_matches': True})
    module = audit.PREFIX+'Rule30ExactReturnResearch'
    rel = Path('lean/Ruliology/CellularAutomata/Rule30ExactReturnResearch.lean')
    source = (audit.ROOT/rel).read_text(encoding='utf-8')
    if tag == 'pinned':
        source = source.removeprefix('module\n').replace('public import ', 'import ').replace('@[expose] public section', '')
        target = project/rel
        if target.exists() and target.read_text(encoding='utf-8') != source:
            raise RuntimeError('Refusing to overwrite different proof source')
        target.write_text(source, encoding='utf-8', newline='\n')
    checked = (project/rel).read_bytes()
    expected_checker = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == expected_checker
    evidence = audit.HERE/'exact-return-evidence'/tag
    evidence.mkdir(parents=True, exist_ok=True)
    audit.run([args.lake, 'build', module], project, evidence/'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
    for h in ['exactReturn_iff_nearSpaced', 'translation_iff_nearSpaced',
              'returnAt_transformed_forces_white', 'transformed_exactReturn_iff',
              'infinite_gate_fails_arbitrarily_late', 'empty_gate_blocks_second_return',
              'empty_gate_fails_arbitrarily_late', 'empty_second_translation_fails',
              'lastAllowed_transformed_return', 'lastAllowed_transformed_not_spaced']:
        argv += ['--headline', module+'.'+h]
    log = evidence/'check.log'
    audit.run(argv, project, log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    assert (project/rel).read_bytes() == checked
    report = {'verdict': 'pass', 'scope': 'exact eight-column return criterion and actual-gate obstruction',
        'full_problem_claim': False, 'new_temporal_period_excluded': False,
        'checker_modified': False, 'source_sha256': hashlib.sha256(checked).hexdigest(),
        'project_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip(),
        'retained_exact_dependency_replays': retained, 'check': data}
    (evidence/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'environment': tag, 'verdict': 'pass', 'constants': data['replay']['constants'],
        'retained_verified_dependency_constants': sum(r['previous_full_replay_constants'] for r in retained)}))


if __name__ == '__main__':
    main()
