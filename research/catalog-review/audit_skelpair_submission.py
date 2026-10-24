"""Replay the exact all-depth period-two reconstruction, submission ad1748."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import urllib.request

HERE = Path(__file__).resolve().parent
KIT = '3eca23c0a9fa6b153313655e6d51835406c2d06e'
ID = 'R30-20261024-ad1748'
URL = 'https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/file?id='+ID+'&kind=lean'
SHA = '153226d13365d8b01d4e85a4ecac57b0556e59c98cdbff1d8dc74f6e39c6daa0'
MODULE = 'Rule30ExternalSkelPairAudit'
HEADS = ['Q01_iff_no_skelPair_support', 'cell_neg_eq_skelPair',
    'skelPair_locality_and_pivot', 'skelPair_even_affine_decomp',
    'even_depth_white_iff_s_eq', 'free_bits_unique_of_even_depths',
    'odd_depth_determined_by_even_depths', 'L_eq_skelPair', 'L_skelRow_eq_skelPair',
    'm5_even', 'm6_odd', 'm7_even', 'm7_odd', 'm8_even', 'm8_odd', 'm9_even', 'm10_even']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--lake', required=True)
    parser.add_argument('--output', type=Path, required=True)
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
    raw = urllib.request.urlopen(URL, timeout=30).read()
    assert hashlib.sha256(raw).hexdigest() == SHA
    target = project/(MODULE+'.lean')
    if target.exists() and target.read_bytes() != raw:
        raise RuntimeError('Different source exists: '+str(target))
    target.write_bytes(raw)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    deps = guard.guarded([args.lake, 'build', 'Rule30PrizeKit',
        'Ruliology.CellularAutomata.Rule30PeriodTwo'], project, output/'dependencies.log')
    artifact = project/'.lake/build/lib/lean'/(MODULE+'.olean')
    artifact.parent.mkdir(parents=True, exist_ok=True)
    build = guard.guarded([args.lake, 'env', 'lean', '-o', str(artifact), str(target)],
        project, output/'build.log')
    print(json.dumps({'stage': 'compiled', 'seconds': build}), flush=True)
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', MODULE, '--claim', 'partial']
    for head in HEADS:
        argv += ['--headline', 'Rule30Submission.'+head]
    log = output/'check.log'
    elapsed = guard.guarded(argv, project, log)
    check = json.loads([line for line in log.read_text(encoding='utf-8').splitlines()
        if line.startswith('{')][-1])
    assert check['verdict'] == 'pass' and check['replay']['ok']
    assert check['replay']['constants'] == 139
    assert not check['newAxioms'] and all(head['ok'] for head in check['headlines'])
    assert target.read_bytes() == raw
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    report = {'verdict': 'pass', 'submission_id': ID,
        'authors': 'G.P.J.W. Quint; Gemini (Google)', 'supersedes': 'R30-20261024-1e1b3b',
        'source_url': URL, 'source_sha256': SHA, 'source_bytes': len(raw),
        'source_adaptations': 'none', 'kit_commit': KIT, 'checker_unchanged': True,
        'checker_sha256': hashlib.sha256(checker).hexdigest(),
        'dependency_build_seconds': deps, 'build_seconds': build, 'replay_seconds': elapsed,
        'check': check, 'Q01_proved': False, 'full_problem_solved': False,
        'scope': 'All-depth free-bit reconstruction and equivalence with still-open Q01; '
                 'golden closed forms assume a coupled alternating center'}
    (output/'skelpair-report.json').write_text(json.dumps(report, indent=2)+'\n',
        encoding='utf-8', newline='\n')
    print(json.dumps({'verdict': 'pass', 'constants': check['replay']['constants'],
        'headlines': len(check['headlines'])}), flush=True)


if __name__ == '__main__': main()
