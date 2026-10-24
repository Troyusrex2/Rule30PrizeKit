"""Measure builds and replay new catalog modules with the unchanged checker."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

import psutil

ap = argparse.ArgumentParser()
ap.add_argument('--project', type=Path, required=True)
ap.add_argument('--output', type=Path, required=True)
ap.add_argument('--skip-build', action='store_true')
ap.add_argument('--lake', required=True)
ap.add_argument('--base', default='cc6867c8fe269c04a60db9fce1720ce2dbb563fb')
args = ap.parse_args()
root = args.project.resolve()
lake = args.lake
args.output.mkdir(parents=True, exist_ok=True)


def run(argv, logfile):
    began = time.monotonic()
    peak = 0
    with logfile.open('w', encoding='utf-8') as out:
        p = subprocess.Popen(argv, cwd=root/'lean', stdout=out, stderr=subprocess.STDOUT)
        task = psutil.Process(p.pid)
        try:
            while p.poll() is None:
                try:
                    owned = [task]+task.children(recursive=True)
                except psutil.NoSuchProcess:
                    owned = []
                rss = 0
                for child in owned:
                    try:
                        rss += child.memory_info().rss
                    except psutil.NoSuchProcess:
                        pass
                peak = max(peak, rss)
                if rss > 8*1024**3 or psutil.virtual_memory().available < 2*1024**3 or time.monotonic()-began > 900:
                    raise RuntimeError('Resource guard; no pass claimed')
                time.sleep(.05)
            if p.returncode:
                raise RuntimeError(logfile.read_text(encoding='utf-8')[-4000:])
        finally:
            if p.poll() is None:
                for child in reversed(task.children(recursive=True)+[task]):
                    try:
                        child.kill()
                    except psutil.NoSuchProcess:
                        pass
                p.wait()
    return {'seconds': time.monotonic()-began, 'peak_owned_RSS_MiB': peak/1024**2}


checker = (root/'Check.lean').read_bytes()
assert checker.replace(b'\r\n', b'\n') == subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=root)
added = subprocess.check_output(['git', 'diff', '--name-only', '--diff-filter=A',
                                args.base+'...HEAD', '--', 'lean'], cwd=root, text=True).splitlines()
modules = [(f, '.'.join(Path(f).with_suffix('').parts[1:])) for f in added if f.endswith('.lean')]
report = {'checker_modified': False, 'full_problem_claim': False,
          'comparison_base': args.base,
          'project_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
          'modules': []}
readme = (root/'lean/README.md').read_text(encoding='utf-8')
for filename, module in modules:
    item = {'module': module, 'source_sha256': hashlib.sha256((root/filename).read_bytes()).hexdigest()}
    if not args.skip_build:
        item['build'] = run([lake, 'build', module], args.output/(module+'.build.log'))
    headlines = []
    for line in readme.splitlines():
        labels = [module.split('.')[-1], module.removeprefix('Ruliology.CellularAutomata.').replace('.', '/')]
        if any(line.startswith('| `'+label+'` |') for label in labels):
            headlines = re.findall(r'`([^`]+)`', line.split('|')[-2])
    assert headlines, 'README headline row missing for '+module
    argv = [lake, 'env', 'lean', '--run', '../Check.lean', module, '--claim', 'partial']
    for name in headlines:
        argv += ['--headline', module+'.'+name]
    log = args.output/(module+'.check.log')
    item['check_resources'] = run(argv, log)
    data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    item['check'] = data
    report['modules'].append(item)
    (args.output/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'module': module, 'constants': data['replay']['constants'],
                      'headlines': len(headlines), 'verdict': 'pass', 'build': item.get('build')}), flush=True)
if not args.skip_build:
    report['full_build'] = run([lake, 'build', 'Ruliology'], args.output/'Ruliology.build.log')
assert (root/'Check.lean').read_bytes() == checker
report['verdict'] = 'pass'
(args.output/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
print(json.dumps({'all_passed': True, 'modules': len(modules), 'full_build': report.get('full_build')}), flush=True)
