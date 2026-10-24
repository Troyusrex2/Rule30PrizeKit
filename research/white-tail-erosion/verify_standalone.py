"""Check the exact essay source against the unchanged current reference checker."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'overnight'))
from audit_contributions import run


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project', type=Path, required=True)
    ap.add_argument('--lake', required=True)
    args = ap.parse_args()
    project = args.project.resolve()
    manifest = json.loads((HERE / 'source-manifest.json').read_text())
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project,
                                   text=True).strip() == manifest['reference_commit']
    checker = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project / 'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    body = (HERE / 'Rule30WhiteTailErosionStandalone.lean').read_text(encoding='utf-8')
    embedded = 'import Rule30PrizeKit\n' + body
    essay = (HERE / 'white-tail-erosion-essay.md').read_text(encoding='utf-8')
    strings = re.findall(r'LeanImportString\[("(?:\\.|[^"\\])*")', essay)
    assert len(strings) == 1 and json.loads(strings[0]) == embedded
    sha = hashlib.sha256(embedded.encode('utf-8')).hexdigest()
    assert sha == manifest['embedded_source_sha256']
    imports = re.findall(r'^import (\S+)$', embedded, re.M)
    assert imports == ['Rule30PrizeKit', 'Ruliology.CellularAutomata.Rule30Prize',
                       'Ruliology.CellularAutomata.Rule30EtherThree']
    module = 'Rule30WhiteTailErosionEssayReplay'
    target = project / (module + '.lean')
    raw = embedded.encode('utf-8')
    if target.exists() and target.read_bytes() != raw:
        raise RuntimeError('Refusing to overwrite different proof source')
    target.write_bytes(raw)
    evidence = HERE / 'standalone-evidence'
    evidence.mkdir(exist_ok=True)
    output = project / '.lake/build/lib/lean' / (module + '.olean')
    compile_seconds = run([args.lake, 'env', 'lean', '-o', str(output), str(target)],
                          project, evidence / 'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
    for h in manifest['headlines']:
        argv += ['--headline', h]
    log = evidence / 'check.log'
    check_seconds = run(argv, project, log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines()
                       if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    assert target.read_bytes() == raw
    assert (project / 'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker
    report = {'verdict': 'pass', 'reference_commit': manifest['reference_commit'],
              'checker_modified': False, 'source_sha256': sha, 'embedded_source_matches': True,
              'imports': imports, 'unmerged_dependency_imported': False,
              'full_problem_claim': False, 'prize_api_submitted': False,
              'compile_seconds': round(compile_seconds, 3),
              'check_seconds': round(check_seconds, 3), 'check': data}
    (evidence / 'report.json').write_text(json.dumps(report, indent=2)+'\n',
                                        encoding='utf-8', newline='\n')
    print(json.dumps({'verdict': 'pass', 'constants': data['replay']['constants'],
                      'headlines': len(data['headlines']), 'embedded_source_matches': True}),
          flush=True)


if __name__ == '__main__':
    main()
