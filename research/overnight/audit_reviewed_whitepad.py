"""Independently replay the reviewed PR 4 revision in an isolated pinned kit."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import audit_contributions as audit

REVISION = '993cb1b61164a1833788881128437ee9fb943627'
STEM = 'Rule30WhitePad10111'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project', type=Path, required=True)
    ap.add_argument('--lake', required=True)
    args = ap.parse_args(); project = args.project.resolve(); module = audit.PREFIX+STEM
    rel = Path('lean/Ruliology/CellularAutomata')/(STEM+'.lean')
    raw = subprocess.check_output(['git', 'show', REVISION+':'+rel.as_posix()], cwd=audit.ROOT)
    source = raw.decode('utf-8').removeprefix('module\n').replace('public import ', 'import ')
    source = source.replace('@[expose] public section', '')
    target = project/rel
    if target.exists() and target.read_text(encoding='utf-8') != source:
        raise RuntimeError('Refusing to overwrite different source')
    target.parent.mkdir(parents=True, exist_ok=True); target.write_text(source, encoding='utf-8', newline='\n')
    expected = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == expected
    evidence = audit.HERE/'reviewed-whitepad-evidence'; evidence.mkdir(exist_ok=True)
    build = audit.run([args.lake, 'build', module], project, evidence/'build.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial',
            '--headline', module+'.not_eventually_zeros_10111']
    log = evidence/'check.log'; check = audit.run(argv, project, log)
    data = json.loads([line for line in log.read_text(encoding='utf-8').splitlines() if line.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    report = {'verdict': 'pass', 'revision': REVISION, 'module': module,
        'original_source_sha256': hashlib.sha256(raw).hexdigest(),
        'reference_source_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
        'checker_modified': False, 'full_problem_claim': False,
        'reference_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip(),
        'adaptation': 'module/export wrappers only; proof bodies unchanged',
        'build_seconds': build, 'check_seconds': check, 'check': data}
    (evidence/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'verdict': 'pass', 'revision': REVISION, 'constants': data['replay']['constants']}))


if __name__ == '__main__': main()
