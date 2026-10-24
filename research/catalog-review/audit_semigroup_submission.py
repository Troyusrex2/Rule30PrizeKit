"""Replay the unchanged public source of submission R30-20261024-9d92a2."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import urllib.request

HERE = Path(__file__).resolve().parent
ID = 'R30-20261024-9d92a2'
URL = 'https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/file?id=' + ID + '&kind=lean'
SHA = '57bd19e546495805c816437239133c694a9ef5ed43a1163b3ad6246f7fe9d1cb'
MODULE = 'Rule30ExternalSemigroupAudit'
HEADS = ['not_eventually_param_word', 'not_eventually_paramWhiteTable',
         'not_eventually_paramBlackTable', 'not_eventually_certTable_finite',
         'Psi_free_constraints_width6_of_finSupp', 'Psi_even_first_defect_le_10',
         'Psi_black_in_window_16', 'psi_empty_997_true', 'no_empty_right_alternating_le_996',
         'not_coupled_of_right_masked_periodic', 'no_empty_right_coupled_0001',
         'no_empty_right_coupled_0011', 'no_empty_right_coupled_0111', 'no_empty_right_coupled_001',
         'skeleton_001_finite', 'skeleton_011_finite', 'q001_width_le_12',
         'inX3_black_in_window_12', 'lc_empty_011_999_true', 'no_empty_right_011_le_998',
         'evol_diff_front', 'exact_death_conf', 'lc_infinite_of_right_masked_periodic',
         'CQ_of_absorption', 'CQ_of_absorptionT']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--lake', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('stripe_replay',
        HERE.parent / 'normalization-first-meeting/replay.py')
    replay = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(replay)
    project = args.project.resolve()
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip() == replay.KIT
    checker = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project / 'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    raw = urllib.request.urlopen(URL, timeout=30).read()
    assert hashlib.sha256(raw).hexdigest() == SHA
    source = project / (MODULE + '.lean')
    if source.exists() and source.read_bytes() != raw:
        raise RuntimeError('Different audit source exists: ' + str(source))
    source.write_bytes(raw)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    artifact = project / '.lake/build/lib/lean' / (MODULE + '.olean')
    seconds = replay.guarded([args.lake, 'env', 'lean', '-o', str(artifact), str(source)],
                             project, output / 'semigroup.build.log')
    print(json.dumps({'stage': 'compiled', 'seconds': seconds}), flush=True)
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', MODULE, '--claim', 'partial']
    for head in HEADS:
        argv += ['--headline', 'Rule30Submission.' + head]
    log = output / 'semigroup.check.log'
    elapsed = replay.guarded(argv, project, log)
    check = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert check['verdict'] == 'pass' and check['replay']['ok'] and not check['newAxioms']
    assert all(h['ok'] for h in check['headlines'])
    report = {'verdict': 'pass', 'submission_id': ID, 'source_url': URL,
              'source_sha256': SHA, 'source_bytes': len(raw), 'source_adaptations': 'none',
              'authors': 'Emerson Villafuerte; Antigravity (Google DeepMind)',
              'kit_commit': replay.KIT, 'checker_unchanged': True,
              'checker_sha256': hashlib.sha256(checker).hexdigest(),
              'build_seconds': seconds, 'replay_seconds': elapsed, 'check': check,
              'scope': 'Independent replay of external partial results; not a proof of EdgeObservable or Problem 1',
              'full_problem_solved': False}
    (output / 'semigroup-report.json').write_text(json.dumps(report, indent=2) + '\n',
                                               encoding='utf-8', newline='\n')
    print(json.dumps({'verdict': 'pass', 'constants': check['replay']['constants'],
                      'headlines': len(check['headlines'])}), flush=True)


if __name__ == '__main__':
    main()
