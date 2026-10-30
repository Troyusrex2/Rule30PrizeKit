"""Portable source-only verification. Requires Lean4.35.0, no packages/network.
python verify.py --lean C:/path/to/lean.exe --out C:/new/empty/directory
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,time

p=argparse.ArgumentParser()
p.add_argument('--lean',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args()
R=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
for name,expected in json.loads((R/'SHA256SUMS.json').read_text()).items():
    rel=Path(name)
    assert not rel.is_absolute() and '..' not in rel.parts
    assert sha(R/rel)==expected,name
lean=a.lean.resolve()
version=subprocess.check_output([str(lean),'--version'],text=True).strip()
assert version.startswith('Lean (version 4.35.0,'),version
assert sha(R/'sources/Check.lean')=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
out=a.out.resolve()
out.mkdir(exist_ok=False)
P=out/'project'
shutil.copytree(R/'sources',P)
env=dict(os.environ,PATH=str(lean.parent)+os.pathsep+os.environ.get('PATH',''),LEAN_NUM_THREADS='1')
env.pop('LEAN_PATH',None)
env.pop('LEAN_SRC_PATH',None)
lake=lean.with_name('lake.exe' if lean.suffix=='.exe' else 'lake')
start=time.monotonic()
def run(args,name):
    with (out/name).open('wb') as stream:
        r=subprocess.run(list(map(str,args)),cwd=P,env=env,stdout=stream,
                         stderr=subprocess.STDOUT,timeout=90)
    if r.returncode:
        print((out/name).read_text(encoding='utf-8',errors='replace')[-5000:])
        raise SystemExit(r.returncode)
module='Ruliology.CellularAutomata.Rule30InverseCascade'
run([lake,'build',module,'StatementGuard'],'build.log')
heads=['finite_cascade_closes','physical_block_closes','scheduled_cascade_closes',
       'exists_reset_schedule','reset_runs_closing','missing_resets_counterexample']
args=[lake,'env',lean,'--run','Check.lean',module,'--claim','partial']
for name in heads:args+=['--headline',module+'.'+name]
run(args,'check.log')
text=(out/'check.log').read_text(encoding='utf-8')
check=json.loads(next(row for row in reversed(text.splitlines()) if row.startswith('{')))
assert check['verdict']=='pass' and check['replay']['ok'] and not check['newAxioms']
assert all(h['ok'] and h['typeMatches'] for h in check['headlines'])
result=dict(passed=True,checker=check,source_warnings='warning:' in (out/'build.log').read_text(encoding='utf-8'),
            seconds=round(time.monotonic()-start,3),lean_version=version,
            lean_sha256=sha(lean),owned_objects_reused=False,whole_catalog_built=False,prize_solved=False)
(out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(passed=True,replay=check['replay'],headlines=len(check['headlines']),
                      new_axioms=check['newAxioms'],source_warnings=result['source_warnings'],seconds=result['seconds'])))
