"""Replay the unbounded terminal-normalizer obstruction at kit 3eca23c."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
KIT = '3eca23c0a9fa6b153313655e6d51835406c2d06e'
MODULE = 'Rule30ResponseGrowthResearch'
HEADS = ['packedRun_cap', 'cap_irreducible', 'run_irreducible', 'run_log2',
         'seven_unbounded', 'packedStep_sound', 'packedRun_sound',
         'constant_output_unbounded_states']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--lake', required=True)
    args = parser.parse_args()
    project = args.project.resolve()
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'],
        cwd=project, text=True).strip() == KIT
    checker = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    spec = importlib.util.spec_from_file_location('resource_guard',
        HERE.parent/'normalization-first-meeting/replay.py')
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    logs = HERE/'logs'
    logs.mkdir(exist_ok=True)
    dependencies = guard.guarded([args.lake, 'build',
        'Ruliology.CellularAutomata.Rule30ControlledResponse'], project, logs/'dependencies.log')
    raw = (HERE/(MODULE+'.lean')).read_bytes()
    target = project/(MODULE+'.lean')
    if target.exists() and target.read_bytes() != raw:
        raise RuntimeError('Different research source exists: '+str(target))
    target.write_bytes(raw)
    artifact = project/'.lake/build/lib/lean'/(MODULE+'.olean')
    artifact.parent.mkdir(parents=True, exist_ok=True)
    build = guard.guarded([args.lake, 'env', 'lean', '-o', str(artifact), str(target)],
        project, logs/'build.log')
    print(json.dumps({'stage': 'compiled', 'seconds': build}), flush=True)
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', MODULE, '--claim', 'partial']
    for head in HEADS:
        argv += ['--headline', 'Rule30ResponseGrowthResearch.'+head]
    log = logs/'check.log'
    elapsed = guard.guarded(argv, project, log)
    check = json.loads([line for line in log.read_text(encoding='utf-8').splitlines()
        if line.startswith('{')][-1])
    assert check['verdict'] == 'pass' and check['replay']['ok']
    assert not check['newAxioms'] and all(head['ok'] for head in check['headlines'])
    assert target.read_bytes() == raw and (HERE/(MODULE+'.lean')).read_bytes() == raw
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    report = {'verdict': 'pass', 'module': MODULE, 'kit_commit': KIT,
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'checker_unchanged': True, 'checker_sha256': hashlib.sha256(checker).hexdigest(),
        'dependency_build_seconds': dependencies, 'build_seconds': build,
        'replay_seconds': elapsed, 'check': check,
        'unbounded_irreducible_growth_proved': True,
        'constant_output_with_unbounded_irreducible_state_proved': True,
        'terminal_rewrite_completeness_proved': False,
        'actual_driver_nonperiodicity_proved': False, 'full_problem_solved': False}
    (HERE/'report.json').write_text(json.dumps(report, indent=2)+'\n',
        encoding='utf-8', newline='\n')
    print(json.dumps({'verdict': 'pass', 'constants': check['replay']['constants'],
        'headlines': len(check['headlines'])}), flush=True)


if __name__ == '__main__':
    main()
