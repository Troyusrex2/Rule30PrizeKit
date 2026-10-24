"""Replay white-tail erosion and its exact, separately credited PR 10 dependency."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import audit_contributions as audit


DEPENDENCY_COMMIT = 'f6885abec122a9dcbb3160cb69312323bc075dc1'
DEPENDENCY = audit.PREFIX + 'Rule30EtherThreeErosion'
MODULE = 'Rule30WhiteTailErosionResearch'
NAMESPACE = audit.PREFIX + MODULE
HEADLINES = ['front_le_witness', 'run_bad_bounded', 'erosion_bounded',
             'white_tail_evol', 'ether_black_within', 'white_tail_defect',
             'white_tail_erosion', 'white_tail_often_departs']


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project', type=Path, required=True)
    ap.add_argument('--lake', required=True)
    args = ap.parse_args()
    project = args.project.resolve()
    reference = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project,
                                        text=True).strip()
    tags = {'cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554': 'historical-pinned',
            '2f63afda261888e04ec57237290e723190914a1d': 'current-reference'}
    if reference not in tags:
        raise RuntimeError('Use a recorded reference checkout')
    checker = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project / 'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    relative = Path('lean') / Path(DEPENDENCY.replace('.', '/')).with_suffix('.lean')
    raw = subprocess.check_output(['git', 'show', DEPENDENCY_COMMIT + ':' + relative.as_posix()],
                                  cwd=audit.ROOT)
    parent = raw.decode('utf-8').removeprefix('module\n').replace('public import ', 'import ')
    parent = parent.replace('@[expose] public section', '').encode('utf-8')
    own = Path(__file__).with_name(MODULE + '.lean').read_bytes()
    evidence = audit.HERE / 'white-tail-erosion-evidence' / tags[reference]
    evidence.mkdir(parents=True, exist_ok=True)
    checked = []
    for name, source, target, headlines in [
        (DEPENDENCY, parent, project / relative,
         [audit.PREFIX + 'Rule30EtherThree.' + h for h in
          ['cert_all', 'front_step', 'wake_good', 'run_bad', 'erosion3_fin', 'no_wall', 'redge_step']]),
        (MODULE, own, project / (MODULE + '.lean'), [NAMESPACE + '.' + h for h in HEADLINES]),
    ]:
        if target.exists() and target.read_bytes() != source:
            raise RuntimeError('Refusing to overwrite different proof source: ' + str(target))
        target.write_bytes(source)
        output_root = (project / 'lean/.lake/build/lib/lean' if name == DEPENDENCY
                       else project / '.lake/build/lib/lean')
        artifact = output_root / Path(name.replace('.', '/')).with_suffix('.olean')
        artifact.parent.mkdir(parents=True, exist_ok=True)
        compile_seconds = audit.run([args.lake, 'env', 'lean', '-o', str(artifact), str(target)],
                                    project, evidence / (name + '.compile.log'))
        argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', name, '--claim', 'partial']
        for h in headlines:
            argv += ['--headline', h]
        log = evidence / (name + '.check.log')
        check_seconds = audit.run(argv, project, log)
        data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines()
                           if s.startswith('{')][-1])
        assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
        assert all(h['ok'] for h in data['headlines'])
        assert target.read_bytes() == source
        checked.append({'module': name, 'source_sha256': hashlib.sha256(source).hexdigest(),
                        'compile_seconds': round(compile_seconds, 3),
                        'check_seconds': round(check_seconds, 3), 'check': data})
        print(json.dumps({'environment': tags[reference], 'module': name, 'verdict': 'pass',
                          'constants': data['replay']['constants']}), flush=True)
    assert (project / 'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    report = {'verdict': 'pass', 'reference_commit': reference, 'checker_modified': False,
              'dependency_commit': DEPENDENCY_COMMIT,
              'dependency_authors': 'Luis Perez Morales; Claude (Fable 5.1)',
              'dependency_source_sha256': hashlib.sha256(raw).hexdigest(),
              'dependency_adaptation': 'Remove module/export wrappers only; no proof-body changes',
              'extension_authors': 'Troy Lowry; OpenAI Codex (GPT-6)',
              'extension_source_unchanged': True, 'problem1_proved': False,
              'period_three_excluded': False, 'new_prize_submission': False, 'modules': checked}
    (evidence / 'report.json').write_text(json.dumps(report, indent=2) + '\n',
                                        encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
