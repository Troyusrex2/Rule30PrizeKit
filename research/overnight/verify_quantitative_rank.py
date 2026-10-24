"""Verify the explicit sparse-rank obstruction and its exact dependencies."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import audit_contributions as audit
import audit_center_runs


def adapt(source):
    return source.removeprefix('module\n').replace('public import ', 'import ').replace('@[expose] public section', '')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project', type=Path, default=audit.ROOT)
    ap.add_argument('--lake', required=True)
    args = ap.parse_args()
    project = args.project.resolve()
    tag = 'catalog' if project == audit.ROOT else 'pinned'
    evidence = audit.HERE/'quantitative-rank-evidence'/tag
    evidence.mkdir(parents=True, exist_ok=True)
    expected = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == expected
    upstream_report = json.loads((audit.HERE/'center-runs-evidence/report.json').read_text(encoding='utf-8'))
    dependencies = []
    for stem, headline in [
            ('Rule30TraceEdgeResearch', 'problem1_of_edgeObservable'),
            ('Rule30PairedTraceResearch', 'no_uniform_sparse_flip_rank'),
            ('Rule30CenterRuns', 'exists_white')]:
        module = audit.PREFIX+stem
        rel = Path('lean/Ruliology/CellularAutomata')/(stem+'.lean')
        source = (audit.ROOT/rel).read_text(encoding='utf-8')
        if stem == 'Rule30CenterRuns':
            raw = subprocess.check_output(['git', 'show', audit_center_runs.REVISION+':'+rel.as_posix()], cwd=audit.ROOT)
            assert hashlib.sha256(raw).hexdigest() == upstream_report['original_source_sha256']
            assert source == raw.decode('utf-8')
        target_source = source if tag == 'catalog' else adapt(source)
        target = project/rel
        assert target.exists() and target.read_text(encoding='utf-8') == target_source
        audit.run([args.lake, 'build', module], project, evidence/(stem+'.build.log'))
        log = evidence/(stem+'.check.log')
        argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
        for h in (audit_center_runs.HEADLINES if stem == 'Rule30CenterRuns' else [headline]):
            argv += ['--headline', module+'.'+h]
        audit.run(argv, project, log)
        data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
        assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
        assert all(h['ok'] for h in data['headlines'])
        dependencies.append({'module': module, 'source_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                             'check': data})
    module = audit.PREFIX+'Rule30QuantitativeRankResearch'
    rel = Path('lean/Ruliology/CellularAutomata/Rule30QuantitativeRankResearch.lean')
    source = (audit.ROOT/rel).read_text(encoding='utf-8')
    if tag == 'pinned':
        source = adapt(source)
        target = project/rel
        if target.exists() and target.read_text(encoding='utf-8') != source:
            raise RuntimeError('Refusing to overwrite different proof source')
        target.write_text(source, encoding='utf-8', newline='\n')
    checked = (project/rel).read_bytes()
    audit.run([args.lake, 'build', module], project, evidence/'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
    for h in ['flipCount_strict_of_ne', 'innerThree_seed_step', 'innerThree_flip_window',
              'innerThree_dyadic_flips', 'sparse_rank_dyadic_lower_bound']:
        argv += ['--headline', module+'.'+h]
    log = evidence/'check.log'
    audit.run(argv, project, log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    assert (project/rel).read_bytes() == checked
    report = {'verdict': 'pass', 'source_sha256': hashlib.sha256(checked).hexdigest(),
        'scope': 'conditional explicit logarithmic sparse-rank lower bound',
        'ranking_constructed': False, 'new_temporal_period_excluded': False, 'full_problem_claim': False,
        'checker_modified': False, 'upstream_center_runs_commit': audit_center_runs.REVISION,
        'reference_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip(),
        'dependencies': dependencies, 'check': data}
    (evidence/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'environment': tag, 'verdict': 'pass', 'constants': data['replay']['constants'],
                      'dependency_constants': [d['check']['replay']['constants'] for d in dependencies]}))


if __name__ == '__main__':
    main()
