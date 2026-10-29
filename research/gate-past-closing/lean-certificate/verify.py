"""Fresh thirteen-source closure; replay every new declaration in all five modules."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,time
arg=argparse.ArgumentParser();arg.add_argument('--lean',type=Path,required=True);arg.add_argument('--out',type=Path,required=True);a=arg.parse_args()
root=Path(__file__).resolve().parent;out=a.out.resolve();out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(a.lean)=='ec7a472d1c12a09b0c0c718f7427c2be527b3f5f07810fdbe076c2507c7a91ea'
assert sha(root/'Check.lean')=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
meta=json.loads((root/'INPUTS.json').read_text())
for f in meta['files']:assert sha(root/f['path'])==f['sha256']
assert sum(f['path'].startswith('sources/') for f in meta['files'])==13
project=out/'project';project.mkdir();shutil.copytree(root/'sources',project/'lean');shutil.copyfile(root/'Check.lean',project/'Check.lean')
(project/'lean/lakefile.toml').write_text('name = "gateclosing"\nversion = "0.1.0"\n[[lean_lib]]\nname = "Ruliology"\n')
env=dict(os.environ,PATH=str(a.lean.parent)+os.pathsep+os.environ.get('PATH',''),LEAN_NUM_THREADS='1');env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
def run(args,name):
    with (out/name).open('wb') as log:r=subprocess.run(args,cwd=project/'lean',env=env,stdout=log,stderr=subprocess.STDOUT)
    if r.returncode:print((out/name).read_text(encoding='utf-8',errors='replace')[-8000:]);r.check_returncode()
prefix='Ruliology.CellularAutomata.'
modules=[
 ('Rule30PastStrip',['tail_of_strip_pair','triangle_sound','future_legal','both_pasts_legal','ten_bit_pasts_differ_at_200']),
 ('Rule30GatePastCover',['allowed_of_prefix','trace_prefix','packed_sound','leaf_sound','prefix_extend','cover_sound','window_bits','root_cover','four_bit_cover_valid','four_bit_cover_bound','four_legal_pasts_agree']),
 ('Rule30Certificates.GatePastCases',[tag+'.'+h for tag in ['Five','Six','Seven'] for h in ['certificates_valid','certificates_bound','legal_pasts_agree']]),
 ('Rule30GatePastCases',[tag+'.legal_pasts_agree' for tag in ['Five','Six','Seven']]),
 ('Rule30GateTailReduction',['closing_equivalence','support_bound_of_common_future','window_successor','stream_gate_legal','periodic_gate_legal','periodic_splicing','gate_rows_infinite_of_all_past_closing','all_pasts_of_finite_covers','gate_rows_infinite_of_finite_covers'])]
start=time.monotonic();lake=a.lean.parent/'lake.exe'
run([str(lake),'build',prefix+'Rule30GatePastCases',prefix+'Rule30GateTailReduction'],'build.log')
checks=[];headlines=[]
for idx,(module,heads) in enumerate(modules):
    full=prefix+module;hs=[full+'.'+h for h in heads];headlines.extend(hs)
    cmd=[str(lake),'env',str(a.lean),'--run',str(project/'Check.lean'),full,'--claim','partial']
    for h in hs:cmd+=['--headline',h]
    log=f'check-{idx}.log';run(cmd,log)
    c=json.loads(next(s for s in reversed((out/log).read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
    assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    checks.append(c);print(json.dumps({'module':full,'constants':c['replay']['constants'],'heads':len(hs)}),flush=True)
types=out/'Types.lean';types.write_text('import '+prefix+'Rule30GatePastCases\nimport '+prefix+'Rule30GateTailReduction\n'+''.join('#check @'+h+'\n#print axioms '+h+'\n' for h in headlines),encoding='utf-8')
run([str(lake),'env',str(a.lean),str(types)],'Types.log')
for f in meta['files']:assert sha(root/f['path'])==f['sha256']
r={'passed':True,'official_pin':meta['pin'],'fresh_source_modules':13,'reused_objects':False,'whole_catalog_build':False,'checkers':checks,'aggregate_constants':sum(c['replay']['constants'] for c in checks),'headline_count':len(headlines),'source_files':meta['files'],'source_warnings':b'warning:' in (out/'build.log').read_bytes(),'seconds':time.monotonic()-start}
assert not r['source_warnings']
(out/'RESULT.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['passed','aggregate_constants','headline_count','seconds','source_warnings']}))
