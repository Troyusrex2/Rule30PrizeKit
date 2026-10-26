from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
r=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert owner.resolve() in r.resolve().parents
p=owner/'research/verifier9-20261026/project';lib=p/'.lake/build/lib/lean'
lean=owner/'_cache/payload/toolchain/bin/lean.exe';checker=p/'Check.lean'
checkhash='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==checkhash
meta=json.loads((r/'pr31-source.json').read_bytes());mode=sys.argv[1];assert mode in ['data','main']
specs={
 'data':('Ruliology.CellularAutomata.Rule30Certificates.WhiteEndNineChecks','WhiteEndNineChecks.lean',
         ['mc_ini','mc_sub','mc_cov','mc_l1','mc_l0','mc_d1','mc_d2']),
 'main':('Ruliology.CellularAutomata.Rule30WhiteEndNine','Rule30WhiteEndNine.lean',
         ['not_eventually_word_mode','modeCert_1e9','not_eventually_one_zero_nine','not_eventually_white_end_ge9'])}
module,filename,heads=specs[mode];source=r/filename
relative='lean/'+module.replace('.','/')+'.lean'
sha=hashlib.sha256(source.read_bytes()).hexdigest();assert sha==meta['files'][relative]
assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',source.read_bytes(),re.M)
target=p/relative;assert not target.exists() or target.read_bytes()==source.read_bytes()
target.write_bytes(source.read_bytes())
if mode=='main':
    previous=json.loads((r/'formal/pr31-data/report.json').read_bytes());assert previous['passed']
    assert previous['compiled_module_sha256']==hashlib.sha256((lib/(specs['data'][0].replace('.','/')+'.olean')).read_bytes()).hexdigest()
out=r/'formal'/('pr31-'+mode);out.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,LEAN_PATH=str(lib),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
manifest=json.loads((p.parent/'source-manifest.json').read_bytes())['files'];stages=[];active=set()
def build(mod,src,external=False):
    dst=lib/(mod.replace('.','/')+'.olean')
    if dst.exists() and not external:return
    assert mod not in active;active.add(mod)
    if not external:assert hashlib.sha256(src.read_bytes()).hexdigest()==manifest[src.relative_to(p).as_posix()]
    for dep in re.findall(r'^(?:public\s+)?import\s+([A-Za-z0-9_.]+)',src.read_text(encoding='utf-8'),re.M):
        if (lib/(dep.replace('.','/')+'.olean')).exists():continue
        candidates=[p/'lean'/(dep.replace('.','/')+'.lean'),p/'equivalents'/(dep.replace('.','/')+'.lean'),p/(dep+'.lean')]
        dependency=next((q for q in candidates if q.exists()),None)
        if dependency is None:assert dep.startswith(('Init','Lean','Std')),dep
        else:build(dep,dependency)
    dst.parent.mkdir(parents=True,exist_ok=True);t=time.monotonic()
    with (out/('build-'+mod+'.log')).open('wb') as f:
        z=subprocess.run([str(lean),'-o',str(dst),str(src.relative_to(p))],cwd=p,env=env,stdout=f,stderr=subprocess.STDOUT)
    stages.append({'module':mod,'exit_code':z.returncode,'seconds':round(time.monotonic()-t,3)})
    if z.returncode:print((out/('build-'+mod+'.log')).read_text(encoding='utf-8',errors='replace')[-5000:],flush=True)
    z.check_returncode();active.remove(mod)
build(module,target,True)
namespace='Ruliology.CellularAutomata.Rule30WhiteEndNine'
argv=[str(lean),'--run',str(checker),module,'--claim','partial']+sum((['--headline',namespace+'.'+h] for h in heads),[])
t=time.monotonic()
with (out/'check.log').open('wb') as f:z=subprocess.run(argv,cwd=p,env=env,stdout=f,stderr=subprocess.STDOUT)
if z.returncode:print((out/'check.log').read_text(encoding='utf-8',errors='replace')[-5000:],flush=True)
z.check_returncode()
c=json.loads(next(x for x in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and all(h['ok'] for h in c['headlines'])
assert hashlib.sha256(checker.read_bytes()).hexdigest()==checkhash
report={'passed':True,'external_author':meta['author'],'head_commit':meta['head_commit'],
 'module':module,'source_sha256':sha,'kit_commit':meta['official_pin_for_replay'],
 'checker_sha256':checkhash,'checker_unchanged':True,'build_stages':stages,'check_seconds':round(time.monotonic()-t,3),
 'check':c,'compiled_module_sha256':hashlib.sha256((lib/(module.replace('.','/')+'.olean')).read_bytes()).hexdigest(),
 'external_work_claimed_as_ours':False,'full_problem_solved':False}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':True,'mode':mode,'replayed':c['replay'],'source_sha256':sha}),flush=True)
