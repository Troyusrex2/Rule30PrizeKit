"""Replay the ancestry calculation and failed short horizon at kit 3eca23c."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
KIT = '3eca23c0a9fa6b153313655e6d51835406c2d06e'
MODULE = 'Rule30AncestryResearch'
HEADS = ['Phi_log2', 'phiRows_log2', 'finite_ancestry_bound', 'no_parent42',
         'pair17_prefix', 'pair17_difference', 'pair17_same_edge',
         'short_ancestry_horizon_counterexample']
ITEMS = [(MODULE, 'Rule30AncestryResearch.', HEADS),
         ('Rule30AncestryCatalogBridge', 'Rule30AncestryCatalogBridge.',
          ['Phi_agrees', 'phiRows_agree', 'prefix_agrees',
           'official_short_ancestry_horizon_counterexample'])]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--lake', required=True)
    parser.add_argument('--output', type=Path, default=HERE/'evidence/ancestry-3eca')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('resource_guard',
        HERE.parent/'normalization-first-meeting/replay.py')
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    project = args.project.resolve()
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'],
        cwd=project, text=True).strip() == KIT
    checker = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    dependency_time = guard.guarded([args.lake, 'build',
        'Ruliology.CellularAutomata.Rule30StripeMeeting'], project, output/'dependencies.log')
    records = []
    for module, namespace, heads in ITEMS:
        source = HERE/(module+'.lean')
        raw = source.read_bytes()
        target = project/source.name
        if target.exists() and target.read_bytes() != raw:
            raise RuntimeError('Different research source exists: '+str(target))
        target.write_bytes(raw)
        artifact = project/'.lake/build/lib/lean'/(module+'.olean')
        artifact.parent.mkdir(parents=True, exist_ok=True)
        build = guard.guarded([args.lake, 'env', 'lean', '-o', str(artifact), str(target)],
            project, output/(module+'.build.log'))
        print(json.dumps({'module': module, 'stage': 'compiled', 'seconds': build}), flush=True)
        argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
        for head in heads:
            argv += ['--headline', namespace+head]
        log = output/(module+'.check.log')
        elapsed = guard.guarded(argv, project, log)
        check = json.loads([line for line in log.read_text(encoding='utf-8').splitlines()
            if line.startswith('{')][-1])
        assert check['verdict'] == 'pass' and check['replay']['ok']
        assert not check['newAxioms'] and all(head['ok'] for head in check['headlines'])
        assert target.read_bytes() == raw and source.read_bytes() == raw
        records.append({'module': module, 'source_sha256': hashlib.sha256(raw).hexdigest(),
            'build_seconds': build, 'replay_seconds': elapsed, 'check': check})
        print(json.dumps({'module': module, 'verdict': 'pass',
            'constants': check['replay']['constants'], 'headlines': len(check['headlines'])}), flush=True)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    report = {'verdict': 'pass', 'modules': records, 'kit_commit': KIT,
        'checker_unchanged': True, 'checker_sha256': hashlib.sha256(checker).hexdigest(),
        'dependency_build_seconds': dependency_time,
        'finite_ancestry_bound_proved': True,
        'short_ancestry_horizon_refuted': True,
        'infinite_trace_ancestry_recovery_proved': False,
        'edge_horizon_refuted': False, 'full_problem_solved': False}
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n',
        encoding='utf-8', newline='\n')
    print(json.dumps({'verdict': 'pass',
        'constants': sum(record['check']['replay']['constants'] for record in records),
        'headlines': sum(len(record['check']['headlines']) for record in records)}), flush=True)


if __name__ == '__main__':
    main()
