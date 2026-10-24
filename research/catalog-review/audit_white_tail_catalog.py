"""Replay the reviewable catalog extension and unchanged PR 10 dependency."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'overnight'))
import audit_contributions as audit
from verify_white_tail_erosion import DEPENDENCY_COMMIT, HEADLINES


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project', type=Path, required=True)
    ap.add_argument('--lake', required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--dependency-commit', default=DEPENDENCY_COMMIT)
    ap.add_argument('--dependency-namespace', default='Rule30EtherThree',
                    choices=['Rule30EtherThree', 'Rule30EtherThreeErosion'])
    args = ap.parse_args()
    root = args.project.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
    checker = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=root)
    assert (root / 'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    module = audit.PREFIX + 'Rule30WhiteTailErosion'
    source = root / 'lean' / Path(module.replace('.', '/')).with_suffix('.lean')
    research = audit.HERE / 'Rule30WhiteTailErosionResearch.lean'
    adapted = source.read_text(encoding='utf-8').removeprefix('module\n\n')
    adapted = adapted.replace('public import ', 'import ').replace('@[expose] public section\n\n', '')
    adapted = adapted.replace(
        'open Rule30Jen Rule30Ether Rule30EtherThree Rule30EtherThreeErosion\n',
        'open Rule30Jen Rule30Ether Rule30EtherThree\n')
    adapted = adapted.replace(module, module + 'Research')
    assert adapted == research.read_text(encoding='utf-8')
    items = [('Rule30EtherThreeErosion', args.dependency_namespace,
              ['cert_all', 'front_step', 'wake_good', 'run_bad', 'erosion3_fin', 'no_wall', 'redge_step']),
             ('Rule30WhiteTailErosion', 'Rule30WhiteTailErosion', HEADLINES)]
    report = {'verdict': 'incomplete', 'project_commit': head, 'checker_modified': False,
              'comparison_base': '2f63afda261888e04ec57237290e723190914a1d',
              'dependency_commit': args.dependency_commit,
              'dependency_namespace': args.dependency_namespace,
              'dependency_authors': 'Luis Perez Morales; Claude (Fable 5.1)',
              'extension_authors': 'Troy Lowry; OpenAI Codex (GPT-6)',
              'research_to_catalog': 'module/export wrappers, namespace, and an open for the renamed upstream namespace only',
              'research_source_sha256': hashlib.sha256(research.read_bytes()).hexdigest(),
              'problem1_proved': False, 'period_three_excluded': False, 'modules': []}
    for stem, namespace, headlines in items:
        name = audit.PREFIX + stem
        relative = Path('lean') / Path(name.replace('.', '/')).with_suffix('.lean')
        raw = (root / relative).read_bytes()
        if stem == 'Rule30EtherThreeErosion':
            original = subprocess.check_output(['git', 'show', args.dependency_commit + ':' + relative.as_posix()], cwd=root)
            assert raw == original
        build_seconds = audit.run([args.lake, 'build', name], root,
                                  args.output / (stem + '.build.log'))
        argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', name, '--claim', 'partial']
        for h in headlines:
            argv += ['--headline', audit.PREFIX + namespace + '.' + h]
        log = args.output / (stem + '.check.log')
        check_seconds = audit.run(argv, root, log)
        data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines()
                           if s.startswith('{')][-1])
        assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
        assert all(h['ok'] for h in data['headlines'])
        assert (root / relative).read_bytes() == raw
        report['modules'].append({'module': name, 'source_sha256': hashlib.sha256(raw).hexdigest(),
                                  'build_seconds': round(build_seconds, 3),
                                  'check_seconds': round(check_seconds, 3), 'check': data})
        print(json.dumps({'module': name, 'verdict': 'pass',
                          'constants': data['replay']['constants']}), flush=True)
    report['warm_catalog_build_seconds'] = audit.run(
        [args.lake, 'build', 'Ruliology'], root, args.output / 'Ruliology.build.log')
    assert (root / 'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == head
    report['verdict'] = 'pass'
    (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n',
                                           encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
