"""Build exact public source; replay every declaration using unchanged Check.lean."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
key=sys.argv[1]
specs={'Rule30WhiteEndNine':['fimage_mem','not_eventually_word_mode','modeCert_pumped','pumpCheck_12','pumpCheck_12_nine','modeCert_nine','modeCert_white_end','not_eventually_white_end_ge9'],
       'Rule30PaddedWords':['eventuallyWord_swap','not_eventuallyWord_zeros_one','no_padded_word']}
heads=specs[key];module='Ruliology.CellularAutomata.'+key
reference=owner/'research/verifier9-20261026/project'
checker=reference/'Check.lean';expected='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==expected
lean=owner/'_cache/payload/toolchain/bin/lean.exe';lib=root/'lib'
compiled=lib.joinpath(*module.split('.')).with_suffix('.olean');compiled.parent.mkdir(parents=True,exist_ok=True)
out=root/'formal'/key;out.mkdir(parents=True,exist_ok=True)
source=root/(key+'.lean');raw=source.read_bytes()
assert hashlib.sha256(raw).hexdigest()==json.loads((root/'public-source.json').read_bytes())['sources'][module]['sha256']
assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',raw,re.M)
env=dict(os.environ,LEAN_PATH=str(lib)+';'+str(reference/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
start=time.monotonic()
def run(argv,log,cwd):
    with log.open('wb') as stream:
        process=subprocess.run(argv,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
    if process.returncode:
        print(log.read_text(encoding='utf-8',errors='replace')[-4000:]);process.check_returncode()
run([str(lean),'-o',str(compiled),str(source)],out/'build.log',root)
compile_seconds=time.monotonic()-start
argv=[str(lean),'--run',str(checker),module,'--claim','partial']
for head in heads:argv+=['--headline',module+'.'+head]
run(argv,out/'check.log',reference)
report=json.loads(next(x for x in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
assert report['verdict']=='pass' and report['replay']['ok'] and not report['newAxioms'] and all(h['ok'] for h in report['headlines'])
assert hashlib.sha256(checker.read_bytes()).hexdigest()==expected
data={'passed':True,'module':module,'source_sha256':hashlib.sha256(raw).hexdigest(),'compiled_module_sha256':hashlib.sha256(compiled.read_bytes()).hexdigest(),'checker_sha256':expected,'pin':'5473ffd075f63c9d626e63b8455805d4831b39ca','compile_seconds':compile_seconds,'total_seconds':time.monotonic()-start,'checker':report}
(out/'report.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print(f'{key}: full replay pass, {report["replay"]["constants"]} constants.')
