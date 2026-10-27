"""Rebuild all bundled sources into a new output directory and use the pinned checker.

The official library must already have been built from the pin in summary.json.
No existing object files are copied from this bundle or from private worker phases.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def verify_bundle():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_bytes())
    for item in manifest['files']:
        rel = Path(item['path'])
        require(not rel.is_absolute() and '..' not in rel.parts, 'Unsafe manifest path')
        path = (ROOT / rel).resolve()
        require(path.is_relative_to(ROOT), 'Manifest path escapes bundle')
        require(path.is_file() and sha(path) == item['sha256'], 'Hash mismatch: ' + item['path'])
    summary = json.loads((ROOT / 'summary.json').read_bytes())
    require(summary['pin'] == '5473ffd075f63c9d626e63b8455805d4831b39ca', 'Unexpected pin')
    require(summary['checker_sha256'] == 'b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905', 'Unexpected checker hash')
    require(summary['build_order'] == json.loads((ROOT / 'build-order.json').read_bytes()), 'Order mismatch')
    seen = set()
    for item in summary['modules']:
        name = item['module']
        require(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', name), 'Invalid module name')
        require(name not in seen and set(item['private_imports']) <= seen, 'Invalid dependency order')
        source = ROOT / 'sources' / (name + '.lean')
        require(sha(source) == item['source_sha256'], 'Source mismatch: ' + name)
        old = json.loads((ROOT / 'formal' / name / 'report.json').read_bytes())
        require(old['passed'] and old['source_sha256'] == item['source_sha256'], 'Evidence mismatch: ' + name)
        require(old['pin'] == summary['pin'] and old['checker_sha256'] == summary['checker_sha256'], 'Evidence pin mismatch')
        check = old['checker']
        require(check['module'] == name and check['verdict'] == 'pass' and check['replay']['ok'] and not check['newAxioms'], 'Invalid root receipt')
        require(check['replay']['constants'] == item['constants'], 'Constant count mismatch')
        require([h['name'] for h in check['headlines']] == item['headlines'], 'Headline mismatch')
        require(all(h['ok'] and h['typeMatches'] for h in check['headlines']), 'Invalid headline receipt')
        seen.add(name)
    require([m['module'] for m in summary['modules']] == summary['build_order'], 'Summary order mismatch')
    require(len(seen) == summary['module_count'], 'Module count mismatch')
    require(sum(m['constants'] for m in summary['modules']) == summary['constants'], 'Total count mismatch')
    return summary

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-only', action='store_true', help='Check bundle hashes and stored root receipts; do not invoke Lean')
    for name in ['lean', 'official-lib', 'checker', 'output']:
        parser.add_argument('--' + name, type=Path)
    args = parser.parse_args()
    summary = verify_bundle()
    if args.verify_only:
        print(json.dumps({'bundle_verified': True, 'lean_invoked': False,
                          'modules': summary['module_count'], 'constants': summary['constants']}))
        return
    require(all([args.lean, args.official_lib, args.checker, args.output]),
            '--lean, --official-lib, --checker and --output are required for replay')
    lean, checker, official = args.lean.resolve(), args.checker.resolve(), args.official_lib.resolve()
    require(lean.is_file() and checker.is_file() and official.is_dir(), 'Missing tool or official library')
    require(sha(checker) == summary['checker_sha256'], 'Official checker hash mismatch')
    version = subprocess.check_output([str(lean), '--version'], text=True, timeout=30).strip()
    require(re.search(r'\bversion 4\.35\.0\b', version) is not None, 'Lean version mismatch: ' + version)
    for item in summary['modules']:
        for name in item['official_imports']:
            require((official / Path(*name.split('.'))).with_suffix('.olean').is_file(), 'Missing official import: ' + name)
    out = args.output.resolve()
    for protected in [ROOT, official, checker.parent, lean.parent]:
        require(not out.is_relative_to(protected), 'Output must be separate from bundle, reference library and tools')
    out.mkdir(parents=True, exist_ok=False)
    lib = out / 'lib'
    lib.mkdir()
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(lib), str(official)]), LEAN_NUM_THREADS='1')
    results = []
    for item in summary['modules']:
        name = item['module']
        source = ROOT / 'sources' / (name + '.lean')
        require(sha(source) == item['source_sha256'], 'Source changed during replay')
        local = out / source.name
        shutil.copyfile(source, local)
        old = json.loads((ROOT / 'formal' / name / 'report.json').read_bytes())['checker']
        commands = [[str(lean), '-o', str(lib / (name + '.olean')), str(local)],
                    [str(lean), '--run', str(checker), name, '--claim', 'partial']]
        for headline in item['headlines']:
            commands[1] += ['--headline', headline]
        start = time.monotonic()
        for command, suffix in zip(commands, ['build', 'check']):
            with (out / (name + '.' + suffix + '.log')).open('wb') as stream:
                subprocess.run(command, cwd=out, env=env, stdout=stream,
                               stderr=subprocess.STDOUT, check=True, timeout=300)
        lines = (out / (name + '.check.log')).read_text(encoding='utf-8').splitlines()
        check = json.loads(next(line for line in reversed(lines) if line.startswith('{')))
        require(check['module'] == name and check['verdict'] == 'pass', 'Checker rejected ' + name)
        require(check['replay'] == old['replay'] and not check['newAxioms'], 'Replay mismatch: ' + name)
        require([h['name'] for h in check['headlines']] == item['headlines'], 'New headline mismatch')
        require(all(h['ok'] and h['typeMatches'] for h in check['headlines']), 'Headline rejected')
        results.append({'module': name, 'source_sha256': sha(source),
                        'checker': check, 'seconds': time.monotonic() - start})
        (out / 'progress.json').write_text(json.dumps({'completed': results}, indent=2) + '\n', encoding='utf-8')
        print(json.dumps({'module': name, 'passed': True, 'constants': item['constants']}), flush=True)
    require(sha(checker) == summary['checker_sha256'], 'Checker changed during replay')
    verify_bundle()
    (out / 'receipt.json').write_text(json.dumps({'passed': True, 'lean_version': version,
        'pin': summary['pin'], 'checker_sha256': summary['checker_sha256'], 'prize_solved': False,
        'results': results}, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'passed': True, 'modules': len(results), 'constants': summary['constants'], 'prize_solved': False}))

if __name__ == '__main__':
    main()
