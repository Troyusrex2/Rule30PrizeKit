"""Compile owned outputs and replay with the unchanged current official checker."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,time
root=Path(__file__).resolve().parent
ref=Path(r'D:\MWB\Rule30\current-reference-009005-20261025')
project=root/'owned-verifier';build=project/'owned-build';build.mkdir(parents=True,exist_ok=True)
lake=Path(r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin\lake.exe')
module=sys.argv[1];assert module.isidentifier()
source=root/(module+'.lean');target=project/source.name;shutil.copyfile(source,target)
checker=(ref/'Check.lean').read_bytes()
sha=hashlib.sha256(checker).hexdigest();assert sha=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
(project/'Check.lean').write_bytes(checker)
out=root/'evidence'/module;out.mkdir(exist_ok=True)
(out/'report.json').unlink(missing_ok=True)
for log_name in ['build.log','check.log']:
    (out/log_name).unlink(missing_ok=True)
env=dict(os.environ,LEAN_PATH=str(build),PYTHONDONTWRITEBYTECODE='1')
heads=['all_sites_iff','all_sites_old','all_sites','cell_score_constant','mixed_after_local','mixed_before_zero','after_correct']
commands=[[str(lake),'env','lean','--root='+str(project),'-o',str(build/(module+'.olean')),str(target)],
 [str(lake),'env','lean','--run',str(project/'Check.lean'),module,'--claim','partial']+
 sum((['--headline',module+'.'+h] for h in heads),[])]
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
report={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'kit_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ref,text=True).strip(),
 'checker_sha256':sha,'checker_unchanged':True,'commands':records,'check':checked,'full_problem_solved':False}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'verdict':'pass','module':module,'replay':checked['replay'],'headlines':heads}),flush=True)
