"""Use read-only compiled reference imports and owned outputs, full unchanged replay."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,time
root=Path(__file__).resolve().parent
ref=Path(r'D:\MWB\Rule30\current-reference-3eca-20261024')
project=root/'owned-verifier';build=project/'owned-build'
lake=Path(r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin\lake.exe')
p=argparse.ArgumentParser();p.add_argument('module');p.add_argument('headlines',nargs='+');a=p.parse_args()
assert a.module.isidentifier()
source=root/(a.module+'.lean');target=project/source.name;shutil.copyfile(source,target)
out=root/'evidence'/a.module;out.mkdir(exist_ok=True)
(out/'report.json').unlink(missing_ok=True)
dependency=root.parent/'source-green-20261025T1610/owned-verifier/owned-build'
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(build),str(dependency)]),PYTHONDONTWRITEBYTECODE='1')
checker=(project/'Check.lean').read_bytes()
sha=hashlib.sha256(checker).hexdigest()
assert sha=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
heads=[x if '.' in x else a.module+'.'+x for x in a.headlines]
commands=[[str(lake),'env','lean','--root='+str(project),'-o',str(build/(a.module+'.olean')),str(target)],
          [str(lake),'env','lean','--run',str(project/'Check.lean'),a.module,'--claim','partial']+sum((['--headline',h] for h in heads),[])]
records=[]
for stage,cmd in zip(['build','check'],commands):
    started=time.monotonic();r=subprocess.run(cmd,cwd=ref,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/(stage+'.log')).write_bytes(r.stdout)
    print(r.stdout.decode('utf-8',errors='replace'),flush=True)
    records.append({'stage':stage,'command':cmd,'seconds':time.monotonic()-started,'exit_code':r.returncode})
    r.check_returncode()
checked=json.loads(next(s for s in reversed(r.stdout.decode('utf-8').splitlines()) if s.startswith('{')))
assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
assert all(h['ok'] for h in checked['headlines'])
assert (project/'Check.lean').read_bytes()==checker and source.read_bytes()==target.read_bytes()
report={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'kit_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ref,text=True).strip(),
        'checker_sha256':sha,'checker_unchanged':True,'commands':records,'check':checked,'full_problem_solved':False}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'verdict':'pass','module':a.module,'replay':checked['replay'],'headlines':heads}),flush=True)
