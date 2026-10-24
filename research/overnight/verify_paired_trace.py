"""Replay the paired-row reductions and sparse-family barriers; no prize claim."""
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
    args = ap.parse_args(); project = args.project.resolve()
    module = audit.PREFIX+'Rule30PairedTraceResearch'
    dependency = audit.PREFIX+'Rule30TraceEdgeResearch'
    rel = Path('lean')/Path(module.replace('.', '/')).with_suffix('.lean')
    source = (audit.ROOT/rel).read_text(encoding='utf-8')
    tag = 'catalog' if project == audit.ROOT else 'pinned'
    if tag == 'pinned':
        dependency_rel = Path('lean')/Path(dependency.replace('.', '/')).with_suffix('.lean')
        dependency_source = (audit.ROOT/dependency_rel).read_text(encoding='utf-8')
        dependency_source = dependency_source.removeprefix('module\n').replace('public import ', 'import ').replace('@[expose] public section', '')
        dependency_target = project/dependency_rel
        if dependency_target.exists() and dependency_target.read_text(encoding='utf-8') != dependency_source:
            raise RuntimeError('Refusing to overwrite different dependency source')
        dependency_target.write_text(dependency_source, encoding='utf-8', newline='\n')
        source = source.removeprefix('module\n').replace('public import ', 'import ').replace('@[expose] public section', '')
        target = project/rel
        if target.exists() and target.read_text(encoding='utf-8') != source:
            raise RuntimeError('Refusing to overwrite different proof source')
        target.write_text(source, encoding='utf-8', newline='\n')
    expected = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == expected
    evidence = audit.HERE/'paired-trace-evidence'/tag; evidence.mkdir(parents=True, exist_ok=True)
    audit.run([args.lake, 'build', dependency], project, evidence/'dependency.build.log')
    dependency_log = evidence/'dependency.check.log'
    audit.run([args.lake, 'env', 'lean', '--run', 'Check.lean', dependency, '--claim', 'partial',
               '--headline', dependency+'.problem1_of_edgeObservable'], project, dependency_log)
    dependency_data = json.loads([s for s in dependency_log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert dependency_data['verdict'] == 'pass' and dependency_data['replay']['ok'] and not dependency_data['newAxioms']
    assert all(h['ok'] for h in dependency_data['headlines'])
    audit.run([args.lake, 'build', module], project, evidence/'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
    for headline in ['nested_evol', 'problem1_of_nested_noncoincidence',
                     'nested_noncoincidence_of_flipRanking', 'problem1_of_flipRanking',
                     'sparse_agreement', 'no_black_count_separation_bound', 'no_uniform_sparse_flip_rank']:
        argv += ['--headline', module+'.'+headline]
    log = evidence/'check.log'; audit.run(argv, project, log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    report = {'verdict': 'pass', 'scope': 'conditional all-period reductions and unbounded sparse-family barriers',
        'NestedNoncoincidence_proved': False, 'FlipRanking_constructed': False,
        'full_problem_claim': False, 'checker_modified': False,
        'source_sha256': hashlib.sha256((project/rel).read_bytes()).hexdigest(),
        'project_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip(),
        'dependency_check': dependency_data, 'check': data}
    (evidence/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'environment': tag, 'verdict': 'pass', 'constants': data['replay']['constants']}))


if __name__ == '__main__': main()
