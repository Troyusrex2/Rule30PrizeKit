"""Portable source replay; the supplied official library must be built at the stated pin."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, time

parser = argparse.ArgumentParser()
for name in ['lean','official-lib','checker','output']:
    parser.add_argument('--'+name, required=True, type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
summary = json.loads((root/'summary.json').read_bytes())
assert sha(args.checker) == summary['checker_sha256']
lean, checker, official = args.lean.resolve(), args.checker.resolve(), args.official_lib.resolve()
version = subprocess.check_output([str(lean),'--version'],text=True,timeout=30)
assert '4.35.0' in version, version
out = args.output.resolve()
out.mkdir(parents=True,exist_ok=False)
lib = out/'lib'; lib.mkdir()
env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(lib),str(official)]), LEAN_NUM_THREADS='1')
results = []
for item in summary['root_fresh_replays']:
    name = item['module']
    source = root/'sources'/(name+'.lean')
    assert sha(source) == item['source_sha256']
    local = out/source.name; shutil.copyfile(source,local)
    old = json.loads((root/'formal'/name/'report.json').read_bytes())['checker']
    commands = [[str(lean),'-o',str(lib/(name+'.olean')),str(local)],
                [str(lean),'--run',str(checker),name,'--claim','partial']]
    for headline in old['headlines']:
        commands[1] += ['--headline',headline['name']]
    start = time.monotonic()
    for command,suffix in zip(commands,['build','check']):
        with (out/(name+'.'+suffix+'.log')).open('wb') as stream:
            subprocess.run(command,cwd=out,env=env,stdout=stream,stderr=subprocess.STDOUT,check=True,timeout=300)
    lines = (out/(name+'.check.log')).read_text(encoding='utf-8').splitlines()
    check = json.loads(next(line for line in reversed(lines) if line.startswith('{')))
    assert check['verdict'] == 'pass' and check['replay'] == old['replay'] and not check['newAxioms']
    assert all(h['ok'] and h['typeMatches'] for h in check['headlines'])
    results.append({'module':name,'source_sha256':sha(source),'checker':check,'seconds':time.monotonic()-start})
assert sha(checker) == summary['checker_sha256']
(out/'receipt.json').write_text(json.dumps({'passed':True,'lean_version':version.strip(),'pin':summary['pin'],'results':results},indent=2)+'\n')
print(json.dumps({'passed':True,'modules':len(results),'prize_solved':False}))
