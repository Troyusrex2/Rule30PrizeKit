"""Source-only Lean 4.35.0 rebuild and official checker replay, one thread.
Creates an isolated local output directory; no installations or network.
"""
from pathlib import Path
import argparse,os,re,subprocess,shutil,json,time,uuid,hashlib
R=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--lean',required=True);a=ap.parse_args()
targets={}
for name in ('SeedAutomaton','SeedSections','SectionCompression'):
    d=json.loads((R/(name+'-validation.json')).read_text())
    for c in d['checks']:
        targets[c['module']]=[h['name'] for h in c['checker']['headlines']]
out=R/('replay-'+uuid.uuid4().hex[:10]);out.mkdir()
for f in (R/'project').rglob('*.lean'):
    dest=out/f.relative_to(R/'project');dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(f,dest)
env=os.environ.copy();env['LEAN_PATH']=str(out);env['LEAN_NUM_THREADS']='1'
seen=set();order=[]
def visit(n):
    if n in seen:return
    seen.add(n);src=out/Path(n.replace('.','/')).with_suffix('.lean')
    for dep in re.findall(r'^(?:public )?import (\S+)',src.read_text(encoding='utf-8'),re.M):
        if (out/Path(dep.replace('.','/')).with_suffix('.lean')).exists():visit(dep)
        elif dep.startswith('Ruliology.'):raise RuntimeError('Missing dependency: '+dep)
    order.append(n)
for n in targets:visit(n)
start=time.monotonic();deadline=start+600;checks=[]
def run(cmd,log):
    remaining=deadline-time.monotonic()
    if remaining<=0:raise TimeoutError('Ten-minute total replay deadline')
    p=subprocess.run(cmd,cwd=out,env=env,capture_output=True,text=True,encoding='utf-8',
                     timeout=min(60,remaining))
    (out/log).write_text(p.stdout+p.stderr,encoding='utf-8')
    if p.returncode:raise RuntimeError('Failed '+str(log)+': '+(p.stdout+p.stderr)[-2000:])
    return p.stdout
for n in order:
    src=out/Path(n.replace('.','/')).with_suffix('.lean')
    run([a.lean,'-o',str(src.with_suffix('.olean')),str(src)],n+'.build.log')
for n,heads in targets.items():
    cmd=[a.lean,'--run',str(out/'Check.lean'),n,'--claim','partial']
    for h in heads:cmd+=['--headline',h]
    stdout=run(cmd,n+'.checker.log')
    d=json.loads([l for l in stdout.splitlines() if l.startswith('{')][-1])
    assert d['verdict']=='pass' and d['replay']['ok'] and not d['newAxioms'] and not d['verifiedTargets'],d
    checks.append({'module':n,'checker':d})
result={'pass':True,'seconds':time.monotonic()-start,'directory':str(out),
        'checks':checks,'source_sha256':{n:hashlib.sha256(
        (out/Path(n.replace('.','/')).with_suffix('.lean')).read_bytes()).hexdigest() for n in order}}
(out/'portable-replay.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'pass':True,'seconds':round(result['seconds'],2),'modules':len(order),
                  'target_checks':len(checks),'directory':str(out)}))
