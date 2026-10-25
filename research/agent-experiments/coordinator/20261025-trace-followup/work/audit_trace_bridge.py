"""Fresh full replay of the existing conditional bridge, not a new theorem."""
from pathlib import Path
import hashlib,json,subprocess,time
root=Path(__file__).resolve().parent
ref=Path(r'D:\MWB\Rule30\current-reference-009005-20261025')
lake=Path(r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin\lake.exe')
pin='0090056412733accaa27643d3cbbf982104f2251'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ref,text=True).strip()==pin
checker=(ref/'Check.lean').read_bytes()
sha=hashlib.sha256(checker).hexdigest()
assert sha=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
module='Ruliology.CellularAutomata.Rule30TraceEdge'
source=ref/'lean/Ruliology/CellularAutomata/Rule30TraceEdge.lean'
heads=['problem1_of_edgeObservable','no_eventuallyPeriodic_of_edgeObservable','edges_equal_of_nonnegative']
commands=[[str(lake),'build',module],[str(lake),'env','lean','--run','Check.lean',module,'--claim','partial']+
          sum((['--headline',module+'.'+h] for h in heads),[])]
records=[]
for name,cmd in zip(['build','check'],commands):
    start=time.monotonic();r=subprocess.run(cmd,cwd=ref,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (root/('trace-bridge-'+name+'.log')).write_bytes(r.stdout)
    print(r.stdout.decode('utf-8',errors='replace')[-1200:],flush=True)
    records.append({'stage':name,'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-start})
    r.check_returncode()
c=json.loads(next(line for line in reversed(r.stdout.decode('utf-8').splitlines()) if line.startswith('{')))
assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms']
assert len(c['headlines'])==3 and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
assert (ref/'Check.lean').read_bytes()==checker
record={'pass':True,'kit_commit':pin,'checker_sha256':sha,'checker_unchanged':True,
        'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'commands':records,'check':c,
        'existing_theorem_reaudited':True,'EdgeObservable_proved':False,'full_problem_solved':False}
(root/'trace-bridge-audit.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'pass':True,'replay':c['replay'],'open_hypothesis_not_proved':True}))
