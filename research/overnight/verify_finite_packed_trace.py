"""Replay the finite packed realization bridge with both unchanged checkers."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import audit_contributions as audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', required=True)
    parser.add_argument('--project', type=Path, default=audit.ROOT)
    args = parser.parse_args()
    project = args.project.resolve()
    tag = 'catalog' if project == audit.ROOT else 'pinned'
    module = audit.PREFIX+'Rule30FinitePackedTraceResearch'
    rel = Path('lean')/Path(module.replace('.', '/')).with_suffix('.lean')
    source = (audit.ROOT/rel).read_text(encoding='utf-8')
    dependencies = {}
    for dep in ['Rule30ThreeConeResearch', 'Rule30ThreePrefixResearch',
                'Rule30PackedReconstructionResearch', 'Rule30SpacingRenormalizationResearch']:
        dep_rel = Path('lean')/Path((audit.PREFIX+dep).replace('.', '/')).with_suffix('.lean')
        dep_source = (audit.ROOT/dep_rel).read_text(encoding='utf-8')
        expected = (dep_source if tag == 'catalog' else dep_source.removeprefix('module\n')
                    .replace('public import ', 'import ').replace('@[expose] public section', ''))
        assert (project/dep_rel).read_text(encoding='utf-8') == expected
        dependencies[dep] = hashlib.sha256((project/dep_rel).read_bytes()).hexdigest()
    if tag == 'pinned':
        source = source.removeprefix('module\n').replace('public import ', 'import ').replace('@[expose] public section', '')
        target = project/rel
        if target.exists() and target.read_text(encoding='utf-8') != source:
            raise RuntimeError('Refusing to overwrite different proof source')
        target.write_text(source, encoding='utf-8', newline='\n')
    checked = (project/rel).read_bytes()
    checker = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    evidence = audit.HERE/'finite-packed-trace-evidence'/tag
    evidence.mkdir(parents=True, exist_ok=True)
    audit.run([args.lake, 'build', module], project, evidence/'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
    for headline in ['lc_eq_recon', 'packedConf_right', 'packedConf_center',
                     'packedConf_white', 'packedConf_depth', 'packedConf_agrees',
                     'packedConf_trace', 'packedConf_finite', 'finite_prefix_constructor',
                     'finite_alternating_prefix']:
        argv += ['--headline', module+'.'+headline]
    log = evidence/'check.log'
    audit.run(argv, project, log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines']) and (project/rel).read_bytes() == checked
    report = {'verdict': 'pass', 'checker_modified': False, 'full_problem_claim': False,
              'infinite_periodic_finite_start_constructed': False,
              'scope': 'Soundness of explicit packed finite-prefix realization for arbitrary length, trace, and bounded right half; realization principle already in catalog',
              'source_sha256': hashlib.sha256(checked).hexdigest(),
              'dependency_source_sha256': dependencies,
              'project_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip(),
              'check': data}
    (evidence/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'environment': tag, 'verdict': 'pass', 'constants': data['replay']['constants']}), flush=True)


if __name__ == '__main__':
    main()
