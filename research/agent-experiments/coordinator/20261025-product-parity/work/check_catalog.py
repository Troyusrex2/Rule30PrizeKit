from pathlib import Path
import hashlib,json,subprocess,time
root=Path(__file__).resolve().parent;out=root/'catalog-evidence';out.mkdir(exist_ok=True)
repo=Path(r'D:\MWB\Rule30\product-parity-catalog-20261025')
ref=Path(r'D:\MWB\Rule30\current-reference-009005-20261025')
lake=Path(r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin\lake.exe')
module='Ruliology.CellularAutomata.Rule30ProductParity'
source=repo/'lean/Ruliology/CellularAutomata/Rule30ProductParity.lean'
checker=ref/'Check.lean';sha=hashlib.sha256(checker.read_bytes()).hexdigest()
assert sha=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
for name in ['report.json','core_lake_build.log','kernel_check.log']:(out/name).unlink(missing_ok=True)
heads=[module+'.'+h for h in ['all_ensembles','paired_F2_exact','paired_F2','paired_F2_semantics']]
commands=[[str(lake),'build',module],
 [str(lake),'env','lean','--run',str(checker),module,'--claim','partial']+
 sum((['--headline',h] for h in heads),[])]
records=[]
for stage,cmd in zip(['core_lake_build','kernel_check'],commands):
    start=time.monotonic();p=subprocess.run(cmd,cwd=repo/'lean',stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/(stage+'.log')).write_bytes(p.stdout)
    records.append({'stage':stage,'command':cmd,'seconds':time.monotonic()-start,'exit_code':p.returncode})
    print(p.stdout.decode('utf-8',errors='replace'),flush=True);p.check_returncode()
checked=json.loads(next(s for s in reversed(p.stdout.decode('utf-8').splitlines()) if s.startswith('{')))
assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
assert all(h['ok'] for h in checked['headlines']) and hashlib.sha256(checker.read_bytes()).hexdigest()==sha
report={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'kit_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ref,text=True).strip(),
 'checker_sha256':sha,'checker_unchanged':True,'commands':records,'check':checked,'full_problem_solved':False}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'pass':True,'core_lake_build':True,'replay':checked['replay'],'headlines':heads}))
