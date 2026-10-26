from pathlib import Path
import difflib,json,re
ROOT=Path(__file__).resolve().parent
remote=ROOT/'remote-numerical'
snapshots={json.loads((p/'manifest.json').read_text(encoding='utf-8-sig'))['response_id']:p
           for p in (ROOT/'snapshots').iterdir()}
checks=[]
def clean_json(x):
    if isinstance(x,dict):return {k:clean_json(v) for k,v in x.items() if k!='seconds'}
    if isinstance(x,list):return [clean_json(v) for v in x]
    return x
def normalize_text(s):
    s=s.replace('\r\n','\n').strip()
    s=re.sub(r'elapsed [0-9.]+s','elapsed <runtime>s',s)
    return s
def compare(task,old_path,new_path,kind='json'):
    run=remote/'runs'/task
    rid=json.loads((run/'manifest.json').read_text(encoding='utf-8-sig'))['response_id']
    a=(snapshots[rid]/old_path).read_text(encoding='utf-8-sig')
    b=(run/new_path).read_text(encoding='utf-8-sig')
    if kind=='json':equal=clean_json(json.loads(a))==clean_json(json.loads(b))
    else:equal=normalize_text(a)==normalize_text(b)
    record={'task':task,'old':old_path,'new':new_path,'equal':equal,'kind':kind}
    if not equal and kind!='json':record['first_differences']=list(difflib.unified_diff(a.splitlines(),b.splitlines()))[:16]
    checks.append(record)
compare('sanity','evidence/results.json','reproduced-output/results.json')
compare('sanity','evidence/center.bits','reproduced-output/center.bits','text')
compare('backend-runs','evidence/runs.json','runs.json')
compare('backend-probe','evidence/periodic-census-L14.json','reproduction.log')
for task,path in [('photo-gate','F001_gating_identity.json'),('photo-runs','F002_restrike_runs.json'),
                  ('photo-control','F002_control_random_orbits.json')]:
    compare(task,'evidence/'+path,'evidence/'+path)
for task,path in [('ml-sideways','sideways_sat_count.json'),('ml-control','control_and_sweep.json'),
                  ('ml-transient','transient_test.json'),('ml-density','defect_depth_profile.json')]:
    compare(task,'evidence/'+path,'evidence/'+path)
for task,path in [('swarm-agreement','dyadic_centercol_T60000.txt'),('swarm-slope','exact_slope_T12000.txt')]:
    compare(task,'evidence/'+path,'reproduction.log','text')
for task,path in [('wiki-gas','01-slip-gas.txt'),('wiki-density','02-density-floor.txt'),
                  ('wiki-sweep','03-single-slip-sweep.txt'),('wiki-clock','04-geometric-clock.txt'),
                  ('wiki-achievable','05-achievable-slips.txt'),('wiki-94','06-verify-94.txt')]:
    compare(task,'logs/'+path,'reproduction.log','text')
results={'all_equal_after_runtime_normalization':all(c['equal'] for c in checks),'checks':checks,
         'finite_only':True,'Lean_verified':False}
(ROOT/'reproduction-comparison.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps({'comparisons':len(checks),'all_equal':results['all_equal_after_runtime_normalization'],
                  'differences':[c for c in checks if not c['equal']]}),flush=True)
