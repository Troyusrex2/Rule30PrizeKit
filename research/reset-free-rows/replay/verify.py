"""Fresh thirteen-source closure; full unchanged replay of all five new modules."""
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
(project/'lean/lakefile.toml').write_text('name = "resetfree"\nversion = "0.1.0"\n[[lean_lib]]\nname = "Ruliology"\n')
env=dict(os.environ,PATH=str(a.lean.parent)+os.pathsep+os.environ.get('PATH',''),LEAN_NUM_THREADS='1');env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
def run(args,name):
    with (out/name).open('wb') as log:r=subprocess.run(args,cwd=project/'lean',env=env,stdout=log,stderr=subprocess.STDOUT)
    if r.returncode:print((out/name).read_text(encoding='utf-8',errors='replace')[-8000:]);r.check_returncode()
prefix='Ruliology.CellularAutomata.'
modules=[
 ('Rule30ResetFreeCore',['path_dead_zero','path_reaches_core','path_eventually_five','all_nodes_checked','graph_valid','encoded_path_eventually_five','encoded_path_five_from_seven','zero_path']),
 ('Rule30ResetFreeRuns',['scan_lt','scan_origin','scan_before_zero','colored_after_zero','exists_coloring']),
 ('Rule30ResetFreeStrip',['packFive_lt','packFive_digit','digits_ext','transition_of_components','atom_table','atom_step_table','vertex_step','encoded_strip_path','colored_strip_five','five_reset_free_rows','avoid_shift','five_reset_free_tails']),
 ('Rule30ResetFreeBoundary',['zrow_recurrence','zrow_five_reset_free_rows','zrow_five_reset_free_tails','one_phase_has_unbounded_resets','not_eventual_avoid','arbitrarily_far_resets_in_five']),
 ('Rule30ResetFreeThree',['transition_of_components','vertex_step','reach_checked','path_to_zero','finite_three_avoid_zero','finite_nonzero_reset_in_three','pair_avoid','pair_step','sharpness_two_rows'])]
start=time.monotonic();lake=a.lean.parent/'lake.exe'
run([str(lake),'build',prefix+'Rule30ResetFreeBoundary',prefix+'Rule30ResetFreeThree'],'build.log')
checks=[];headlines=[]
for idx,(module,heads) in enumerate(modules):
    full=prefix+module;hs=[full+'.'+h for h in heads];headlines.extend(hs)
    cmd=[str(lake),'env',str(a.lean),'--run',str(project/'Check.lean'),full,'--claim','partial']
    for h in hs:cmd+=['--headline',h]
    log=f'check-{idx}.log';run(cmd,log)
    c=json.loads(next(s for s in reversed((out/log).read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
    assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    checks.append(c);print(json.dumps({'module':full,'constants':c['replay']['constants'],'heads':len(hs)}),flush=True)
types=out/'Types.lean';types.write_text('import '+prefix+'Rule30ResetFreeBoundary\nimport '+prefix+'Rule30ResetFreeThree\n'+''.join('#check @'+h+'\n#print axioms '+h+'\n' for h in headlines),encoding='utf-8')
run([str(lake),'env',str(a.lean),str(types)],'Types.log')
for f in meta['files']:assert sha(root/f['path'])==f['sha256']
r={'passed':True,'official_pin':meta['pin'],'fresh_source_modules':13,'reused_objects':False,'whole_catalog_build':False,'checkers':checks,'aggregate_constants':sum(c['replay']['constants'] for c in checks),'headline_count':len(headlines),'source_files':meta['files'],'source_warnings':b'warning:' in (out/'build.log').read_bytes(),'seconds':time.monotonic()-start}
assert not r['source_warnings']
(out/'RESULT.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['passed','aggregate_constants','headline_count','seconds','source_warnings']}))
