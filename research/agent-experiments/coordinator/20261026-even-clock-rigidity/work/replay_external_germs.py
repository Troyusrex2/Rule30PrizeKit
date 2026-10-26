from pathlib import Path
import subprocess,os,json,hashlib,re,time
r=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert owner.resolve() in r.resolve().parents
p=owner/'research/verifier9-20261026/project';lib=p/'.lake/build/lib/lean'
lean=owner/'_cache/payload/toolchain/bin/lean.exe';checker=p/'Check.lean'
expected='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==expected
source=r/'Rule30CoupledGerms.lean';meta=json.loads((r/'external-germs-source.json').read_bytes())
assert hashlib.sha256(source.read_bytes()).hexdigest()==meta['source_sha256']
assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',source.read_bytes(),re.M)
target=p/'lean/Ruliology/CellularAutomata/Rule30CoupledGerms.lean'
assert not target.exists() or target.read_bytes()==source.read_bytes()
target.write_bytes(source.read_bytes())
env=dict(os.environ,LEAN_PATH=str(lib),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
out=r/'formal/Rule30CoupledGerms';out.mkdir(parents=True,exist_ok=True);stages=[];active=set()
manifest=json.loads((p.parent/'source-manifest.json').read_bytes())['files']
def build(module,src,external=False):
    dst=lib/(module.replace('.','/')+'.olean')
    if dst.exists() and not external:return
    assert module not in active;active.add(module)
    if not external:
        name=src.relative_to(p).as_posix();assert hashlib.sha256(src.read_bytes()).hexdigest()==manifest[name]
    for name in re.findall(r'^(?:public\s+)?import\s+([A-Za-z0-9_.]+)',src.read_text(encoding='utf-8'),re.M):
        cached=lib/(name.replace('.','/')+'.olean')
        if cached.exists():continue
        candidates=[p/'lean'/(name.replace('.','/')+'.lean'),p/'equivalents'/(name.replace('.','/')+'.lean'),p/(name+'.lean')]
        dep=next((x for x in candidates if x.exists()),None)
        if dep is None:
            assert name.startswith(('Init','Lean','Std')),name
        else:build(name,dep)
    dst.parent.mkdir(parents=True,exist_ok=True);log=out/('build-'+module+'.log');t=time.monotonic()
    with log.open('wb') as f:z=subprocess.run([str(lean),'-o',str(dst),str(src.relative_to(p))],cwd=p,env=env,stdout=f,stderr=subprocess.STDOUT)
    stages.append({'module':module,'exit_code':z.returncode,'seconds':round(time.monotonic()-t,3)})
    if z.returncode:print(log.read_text(encoding='utf-8',errors='replace')[-6000:],flush=True)
    z.check_returncode();active.remove(module)
module='Ruliology.CellularAutomata.Rule30CoupledGerms';build(module,target,external=True)
heads=[module+'.'+s for s in ['right_root_gamma_transport','right_root_periodic_of_zero_gamma',
 'coupled_left_periodic_of_zero_gamma','coupled_zero_gamma_impossible_of_left_edge',
 'finite_config_zero_gamma_impossible','coupled_gamma_cofinal_of_left_edge','coupled_finite_gamma_cofinal']]
argv=[str(lean),'--run',str(checker),module,'--claim','partial']+sum((['--headline',h] for h in heads),[])
t=time.monotonic()
with (out/'check.log').open('wb') as f:z=subprocess.run(argv,cwd=p,env=env,stdout=f,stderr=subprocess.STDOUT)
if z.returncode:print((out/'check.log').read_text(encoding='utf-8',errors='replace')[-6000:],flush=True)
z.check_returncode()
c=json.loads(next(x for x in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and all(h['ok'] for h in c['headlines'])
assert hashlib.sha256(checker.read_bytes()).hexdigest()==expected
report={'passed':True,'external_author':meta['author'],'external_head_commit':meta['head_commit'],
 'source_sha256':meta['source_sha256'],'kit_commit':meta['official_pin_for_replay'],
 'checker_sha256':expected,'checker_unchanged':True,'build_stages':stages,'check_seconds':time.monotonic()-t,
 'check':c,'new_result_claimed_by_this_agent':False,'full_problem_solved':False}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':True,'external_author':meta['author'],'replay':c['replay'],'source_sha256':meta['source_sha256']}),flush=True)
