"""Build the complete core catalog in dependency order with one module at a time.

This bounds concurrent compiler processes on memory-limited machines. It does
not modify proof sources, checker policy, build settings, or machine settings.
Run verify_catalog.py separately to replay contributed declarations.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

import psutil


def module_order(source):
    paths = {'.'.join(p.relative_to(source).with_suffix('').parts): p
             for p in source.rglob('*.lean') if '.lake' not in p.relative_to(source).parts}
    imports = {m: [d for d in re.findall(r'^\s*(?:public\s+)?import\s+(\S+)',
                                       p.read_text(encoding='utf-8'), re.M) if d in paths]
               for m, p in paths.items()}
    order, visiting, visited = [], set(), set()

    def visit(m):
        if m in visited:
            return
        if m in visiting:
            raise RuntimeError('Import cycle at '+m)
        visiting.add(m)
        for d in imports[m]:
            visit(d)
        visiting.remove(m)
        visited.add(m)
        order.append(m)

    for m in sorted(paths):
        visit(m)
    return order, paths


def run(lake, module, source, logfile):
    began, peak = time.monotonic(), 0
    with logfile.open('w', encoding='utf-8') as out:
        process = subprocess.Popen([lake, 'build', module], cwd=source,
                                   stdout=out, stderr=subprocess.STDOUT)
        parent = psutil.Process(process.pid)
        try:
            while process.poll() is None:
                try:
                    owned = parent.children(recursive=True)+[parent]
                except psutil.NoSuchProcess:
                    owned = []
                rss = 0
                for child in owned:
                    try:
                        rss += child.memory_info().rss
                    except psutil.NoSuchProcess:
                        pass
                peak = max(peak, rss)
                if (rss > 8*1024**3 or psutil.virtual_memory().available < 2*1024**3
                        or time.monotonic()-began > 900):
                    raise RuntimeError('Resource guard; no successful build claimed')
                time.sleep(.05)
            if process.returncode:
                raise RuntimeError(logfile.read_text(encoding='utf-8')[-4000:])
        finally:
            if process.poll() is None:
                for child in parent.children(recursive=True)+[parent]:
                    try:
                        child.kill()
                    except psutil.NoSuchProcess:
                        pass
                process.wait()
    return {'seconds': time.monotonic()-began, 'peak_owned_RSS_MiB': peak/1024**2}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--lake', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = args.project.resolve()
    source = root/'lean'
    order, paths = module_order(source)
    assert 'Ruliology' in paths
    hashes = {m: hashlib.sha256(p.read_bytes()).hexdigest() for m, p in paths.items()}
    report = {'project_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                  cwd=root, text=True).strip(), 'source_sha256': hashes,
              'full_problem_solved': False, 'kernel_replay_performed': False,
              'modules': [], 'verdict': 'incomplete'}
    args.output.mkdir(parents=True, exist_ok=True)
    for i, module in enumerate(order):
        result = run(args.lake, module, source, args.output/(module+'.build.log'))
        report['modules'].append({'module': module, **result})
        (args.output/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
        if i % 10 == 0 or i+1 == len(order):
            print(json.dumps({'built': i+1, 'total': len(order), 'module': module}), flush=True)
    assert hashes == {m: hashlib.sha256(p.read_bytes()).hexdigest() for m, p in paths.items()}
    report['verdict'] = 'pass'
    (args.output/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'verdict': 'pass', 'built_modules': len(order)}), flush=True)


if __name__ == '__main__':
    main()
