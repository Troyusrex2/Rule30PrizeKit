"""Fully replay the exact width-74 witness at the updated verifier commit.

The external result is a finite lower bound, not a maximality or prize proof.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import urllib.request

HERE = Path(__file__).resolve().parent
KIT = '3eca23c0a9fa6b153313655e6d51835406c2d06e'
ID = 'R30-20261024-a129c3'
URL = 'https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/file?id=' + ID + '&kind=lean'
SHA = 'b8c5bee5bb3521d11ed27c3fa41b5e4c7ff6b89169488d3fb1e498c51f2c01f8'
MODULE = 'Rule30ExternalWidth74Audit'
HEADS = ['width74_lower', 'w74_dies']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--lake', required=True)
    parser.add_argument('--output', type=Path, required=True)
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
    raw = urllib.request.urlopen(URL, timeout=30).read()
    assert hashlib.sha256(raw).hexdigest() == SHA
    source = project/(MODULE+'.lean')
    if source.exists() and source.read_bytes() != raw:
        raise RuntimeError('Different source exists: ' + str(source))
    source.write_bytes(raw)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    dependencies = guard.guarded([args.lake, 'build', 'Rule30PrizeKit',
        'Ruliology.CellularAutomata.Rule30ZeroBoundarySmall'], project,
        output/'width74-dependencies.log')
    artifact = project/'.lake/build/lib/lean'/(MODULE+'.olean')
    artifact.parent.mkdir(parents=True, exist_ok=True)
    build = guard.guarded([args.lake, 'env', 'lean', '-o', str(artifact), str(source)],
        project, output/'width74-build.log')
    print(json.dumps({'stage': 'compiled', 'seconds': build}), flush=True)
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', MODULE, '--claim', 'partial']
    for head in HEADS:
        argv += ['--headline', 'Rule30Submission.'+head]
    log = output/'width74-check.log'
    elapsed = guard.guarded(argv, project, log)
    check = json.loads([line for line in log.read_text(encoding='utf-8').splitlines()
        if line.startswith('{')][-1])
    assert check['verdict'] == 'pass' and check['replay']['ok']
    assert not check['newAxioms'] and all(head['ok'] for head in check['headlines'])
    report = {'submission_id': ID, 'verdict': 'pass', 'source_url': URL,
        'source_sha256': SHA, 'source_bytes': len(raw), 'source_adaptations': 'none',
        'kit_commit': KIT, 'checker_unchanged': True,
        'checker_sha256': hashlib.sha256(checker).hexdigest(),
        'dependency_build_seconds': dependencies, 'build_seconds': build,
        'replay_seconds': elapsed, 'check': check,
        'scope': 'Explicit width-74 zero-boundary start survives every even time '
                 'below 134 and dies at 134; no maximality, count, or unbounded conclusion',
        'gpu_census_reproduced': False, 'full_problem_solved': False}
    (output/'width74-report.json').write_text(json.dumps(report, indent=2)+'\n',
        encoding='utf-8', newline='\n')
    print(json.dumps({'verdict': 'pass', 'constants': check['replay']['constants'],
        'headlines': len(check['headlines'])}), flush=True)


if __name__ == '__main__':
    main()
