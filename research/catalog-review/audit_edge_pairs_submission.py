"""Replay the exact public source of submission R30-20261024-991a71."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import urllib.request

HERE = Path(__file__).resolve().parent
ID = 'R30-20261024-991a71'
URL = 'https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/file?id=' + ID + '&kind=lean'
SHA = 'dd1e9b87f9f34b839461353f9c9a6ad3a256d6ed4875a1237fd8cbe3fc3f2083'
MODULE = 'Rule30ExternalEdgePairsAudit'
HEADS = ['sep_8', 'sep_13', 'sep_14', 'attained_8', 'attained_13', 'attained_14',
         'separationB', 'centers_spec']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--lake', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--whole-module', action='store_true',
                        help='Use one module; default splits unchanged declarations to keep each replay bounded')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('resource_guard',
        HERE.parent/'normalization-first-meeting/replay.py')
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    project = args.project.resolve()
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip() == guard.KIT
    checker = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    raw = urllib.request.urlopen(URL, timeout=30).read()
    assert hashlib.sha256(raw).hexdigest() == SHA
    if not args.whole_module:
        from audit_edge_pairs_split import replay_split_source
        replay_split_source(project, args.lake, args.output.resolve(), raw, guard, checker)
        return
    source = project/(MODULE+'.lean')
    if source.exists() and source.read_bytes() != raw:
        raise RuntimeError('Different audit source exists: ' + str(source))
    source.write_bytes(raw)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    artifact = project/'.lake/build/lib/lean'/(MODULE+'.olean')
    seconds = guard.guarded([args.lake, 'env', 'lean', '-o', str(artifact), str(source)],
                            project, output/'edge-pairs.build.log')
    print(json.dumps({'stage': 'compiled', 'seconds': seconds}), flush=True)
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', MODULE, '--claim', 'partial']
    for head in HEADS:
        argv += ['--headline', 'Rule30Submission.'+head]
    log = output/'edge-pairs.check.log'
    elapsed = guard.guarded(argv, project, log)
    check = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert check['verdict'] == 'pass' and check['replay']['ok'] and not check['newAxioms']
    assert all(h['ok'] for h in check['headlines'])
    report = {'verdict': 'pass', 'submission_id': ID, 'source_url': URL,
              'source_sha256': SHA, 'source_bytes': len(raw), 'source_adaptations': 'none',
              'authors': 'Gareth Herbert; Claude (Anthropic); GPT (OpenAI)',
              'kit_commit': guard.KIT, 'checker_unchanged': True,
              'checker_sha256': hashlib.sha256(checker).hexdigest(),
              'build_seconds': seconds, 'replay_seconds': elapsed, 'check': check,
              'scope': 'Three fixed left-edge pairs with arbitrary right tails; no uniform all-edge result',
              'full_problem_solved': False}
    (output/'edge-pairs-report.json').write_text(json.dumps(report, indent=2)+'\n',
                                               encoding='utf-8', newline='\n')
    print(json.dumps({'verdict': 'pass', 'constants': check['replay']['constants'],
                      'headlines': len(check['headlines'])}), flush=True)


if __name__ == '__main__':
    main()
