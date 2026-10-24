"""Independently replay public PR sources against the pinned, unchanged checker.

The only source adaptation removes Lean module/export wrappers. Proof bodies and
certificate payloads are preserved. No official submission status is inferred.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

import psutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREFIX = 'Ruliology.CellularAutomata.'
ITEMS = [
    ('origin/pr4-whitepad', 'Rule30Certificates.WhitePadNineWords',
     PREFIX + 'Rule30Certificates.WhitePadNineWords.not_eventually_000000001111'),
    ('origin/pr4-whitepad', 'Rule30WhitePadNineWords',
     PREFIX + 'Rule30WhitePadNineWords.not_eventually_zeros_10111'),
    ('origin/pr5-sparse16', 'Rule30Certificates.Sparse16',
     PREFIX + 'Rule30Sparse16.CheckpointSoundness.step_correct'),
    ('origin/pr5-sparse16', 'Rule30Sparse16',
     PREFIX + 'Rule30Sparse16.fifty_six_even_black_forces_seventeen'),
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(argv, cwd, log, timeout=1200):
    started = time.monotonic()
    with log.open('w', encoding='utf-8', newline='\n') as out:
        p = subprocess.Popen(argv, cwd=cwd, stdout=out, stderr=subprocess.STDOUT)
        task = psutil.Process(p.pid)
        try:
            while p.poll() is None:
                time.sleep(.5)
                try:
                    owned = [task] + task.children(recursive=True)
                except psutil.NoSuchProcess:
                    owned = []
                rss = 0
                for child in owned:
                    try:
                        rss += child.memory_info().rss
                    except psutil.NoSuchProcess:
                        pass
                if (rss > 8 * 1024**3 or psutil.virtual_memory().available < 2 * 1024**3
                        or time.monotonic() - started > timeout):
                    raise RuntimeError('Owned job exceeded resource guard; no pass claimed; '
                                       f'elapsed={time.monotonic()-started:.1f}s, '
                                       f'RSS={rss/1024**3:.2f} GiB')
            if p.returncode:
                raise RuntimeError(log.read_text(encoding='utf-8')[-2000:])
        finally:
            if p.poll() is None:
                try:
                    owned = task.children(recursive=True) + [task]
                except psutil.NoSuchProcess:
                    owned = []
                for child in reversed(owned):
                    try:
                        child.kill()
                    except psutil.NoSuchProcess:
                        pass
                p.wait()
    return time.monotonic() - started


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project', type=Path, required=True)
    ap.add_argument('--lake', required=True)
    ap.add_argument('--timeout-seconds', type=int, default=1200)
    ap.add_argument('--resume', action='store_true')
    args = ap.parse_args()
    project = args.project.resolve()
    evidence = HERE / 'contribution-audit'
    evidence.mkdir(parents=True, exist_ok=True)
    report = {'official_submission_status_checked': False,
              'checker_modified': False, 'proof_bodies_unchanged': True,
              'kit_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project,
                                                    text=True).strip(), 'modules': []}
    report_path = evidence / 'report.json'
    if args.resume and report_path.exists():
        previous = json.loads(report_path.read_text(encoding='utf-8'))
        assert previous['kit_commit'] == report['kit_commit']
        report = previous
    expected_checker = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    # Git may have checked text out with CRLF; compare normalized source.
    assert (project / 'Check.lean').read_bytes().replace(b'\r\n', b'\n') == expected_checker
    for ref, stem, headline in ITEMS:
        rel = Path('lean') / Path((PREFIX + stem).replace('.', '/')).with_suffix('.lean')
        raw = subprocess.check_output(['git', 'show', ref + ':' + rel.as_posix()], cwd=ROOT)
        source = raw.decode('utf-8')
        adapted = source.removeprefix('module\n').replace('public import ', 'import ')
        adapted = adapted.replace('@[expose] public section', '')
        target = project / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and target.read_text(encoding='utf-8') != adapted:
            raise RuntimeError('Refusing to overwrite different source: ' + str(target))
        target.write_text(adapted, encoding='utf-8', newline='\n')
        module = PREFIX + stem
        record = {'module': module, 'upstream_ref': ref,
                  'upstream_commit': subprocess.check_output(['git', 'rev-parse', ref], cwd=ROOT,
                                                             text=True).strip(),
                  'upstream_source_sha256': sha(raw),
                  'adapted_source_sha256': sha(target.read_bytes()), 'headline': headline}
        cached = next((r for r in report['modules'] if r['module'] == module), None)
        if cached is not None and args.resume:
            assert all(cached[k] == record[k] for k in record)
            assert cached['check']['verdict'] == 'pass' and cached['check']['replay']['ok']
            print(json.dumps({'stage': 'retained_exact_source_pass', 'module': module}), flush=True)
            continue
        print(json.dumps({'stage': 'build', 'module': module}), flush=True)
        record['build_seconds'] = run([args.lake, 'build', module], project,
                                       evidence / (stem + '.build.log'), args.timeout_seconds)
        print(json.dumps({'stage': 'full_kernel_replay', 'module': module}), flush=True)
        log = evidence / (stem + '.check.log')
        record['check_seconds'] = run([args.lake, 'env', 'lean', '--run', 'Check.lean', module,
                                      '--claim', 'partial', '--headline', headline], project, log,
                                     args.timeout_seconds)
        data = json.loads([line for line in log.read_text(encoding='utf-8').splitlines()
                           if line.startswith('{')][-1])
        assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
        assert all(h['ok'] for h in data['headlines'])
        record['check'] = data
        report['modules'].append(record)
        (evidence / 'report.json').write_text(json.dumps(report, indent=2) + '\n',
                                             encoding='utf-8', newline='\n')
        print(json.dumps({'stage': 'passed', 'module': module,
                          'constants': data['replay']['constants']}), flush=True)
    report['verdict'] = 'pass'
    (evidence / 'report.json').write_text(json.dumps(report, indent=2) + '\n',
                                         encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
