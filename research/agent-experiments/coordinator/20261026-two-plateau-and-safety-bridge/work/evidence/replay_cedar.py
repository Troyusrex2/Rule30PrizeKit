from pathlib import Path
import hashlib,json,os,re,subprocess,time
root=Path(__file__).resolve().parent
repo=Path(r'D:\MWB\Rule30\overnight-20261024')
pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
lean=Path(r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin\lean.exe')
project=root/'root-replay';project.mkdir()
library=project/'lib';library.mkdir()
logs=project/'logs';logs.mkdir()
source=root/'snapshot/verifier/kit/CedarSafetySoundness.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='e2e17bdb5be676ba8739a477e88e7e0ffc00da58422eb88c4b37303c26165e1a'
assert not re.search(rb'\b(?:sorry|axiom|native_decide|bv_decide)\b|decide\s*\+native|skipKernel',source.read_bytes())
official=['Check.lean','lean/Ruliology/CellularAutomata/Rule30Jen.lean',
          'lean/Ruliology/CellularAutomata/Rule30Prize.lean']
hashes={}
for relative in official:
    data=subprocess.check_output(['git','show',pin+':'+relative],cwd=repo)
    dest=project/relative;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
    hashes[relative]=hashlib.sha256(data).hexdigest()
assert hashes['Check.lean']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
proof=project/'CedarSafetySoundness.lean';proof.write_bytes(source.read_bytes())
env=dict(os.environ,LEAN_PATH=str(library),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
stages=[];start=time.monotonic()
for module,relative in [('Ruliology.CellularAutomata.Rule30Jen',official[1]),
    ('Ruliology.CellularAutomata.Rule30Prize',official[2]),('CedarSafetySoundness','CedarSafetySoundness.lean')]:
    output=library/(module.replace('.','/')+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
    t=time.monotonic()
    with (logs/('build-'+module+'.log')).open('wb') as stream:
        code=subprocess.run([str(lean),'-o',str(output),relative],cwd=project,env=env,stdout=stream,stderr=subprocess.STDOUT)
    stages.append({'module':module,'exit':code.returncode,'seconds':time.monotonic()-t});code.check_returncode()
argv=[str(lean),'--run','Check.lean','CedarSafetySoundness','--claim','partial']
for h in ['accepted_return_eight','local_rule_bridge','run8_cons']:argv+=['--headline','CedarSafetySoundness.'+h]
with (logs/'full-check.log').open('wb') as stream:
    checked=subprocess.run(argv,cwd=project,env=env,stdout=stream,stderr=subprocess.STDOUT)
checked.check_returncode()
report=json.loads(next(x for x in reversed((logs/'full-check.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
assert report['verdict']=='pass' and report['replay']['ok'] and not report['newAxioms']
assert all(h['ok'] for h in report['headlines'])
result={'passed':True,'pin':pin,'source_sha256':hashlib.sha256(proof.read_bytes()).hexdigest(),
        'official_source_hashes':hashes,'fresh_dependency_builds':stages,
        'reference_cache_reused':False,'seconds':time.monotonic()-start,'checker':report}
(project/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('Cedar accepted-language whole-word return independently rebuilt and fully kernel replayed.')
