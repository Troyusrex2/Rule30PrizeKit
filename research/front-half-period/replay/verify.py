"""Fresh five-source Lake build and unchanged official checker replay."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,time
arg=argparse.ArgumentParser();arg.add_argument('--lean',type=Path,required=True);arg.add_argument('--out',type=Path,required=True);a=arg.parse_args()
root=Path(__file__).resolve().parent;out=a.out.resolve();out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(a.lean)=='ec7a472d1c12a09b0c0c718f7427c2be527b3f5f07810fdbe076c2507c7a91ea'
assert sha(root/'Check.lean')=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
meta=json.loads((root/'INPUTS.json').read_text())
for f in meta['files']:assert sha(root/f['path'])==f['sha256']
project=out/'project';project.mkdir();shutil.copytree(root/'sources',project/'lean')
shutil.copyfile(root/'Check.lean',project/'Check.lean')
(project/'lean/lakefile.toml').write_text('name = "clockdrop"\nversion = "0.1.0"\n[[lean_lib]]\nname = "Ruliology"\n')
env=dict(os.environ,PATH=str(a.lean.parent)+os.pathsep+os.environ.get('PATH',''),LEAN_NUM_THREADS='1');env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
def run(args,name):
    with (out/name).open('wb') as log:r=subprocess.run(args,cwd=project/'lean',env=env,stdout=log,stderr=subprocess.STDOUT)
    if r.returncode:print((out/name).read_text(encoding='utf-8',errors='replace')[-7000:]);r.check_returncode()
subprocess.run([os.sys.executable,'-B',str(root/'controls.py')],check=True)
start=time.monotonic();module='Ruliology.CellularAutomata.Rule30FrontHalfPeriod';lake=a.lean.parent/'lake.exe'

for idx,dependency in enumerate(meta['build_order']):run([str(lake),'build',dependency],f'build-{idx:02d}.log')
(out/'build.log').write_bytes(b''.join((out/f'build-{i:02d}.log').read_bytes() for i in range(len(meta['build_order']))))
specs={
 'Ruliology.CellularAutomata.Rule30RightPrefixClock':['growth_antiperiod','exponent_step','no_11011','exists_prefix_exponent','actual_no_11011','actual_recurrence'],
 'Ruliology.CellularAutomata.Rule30RightPrefixBound':['exponent_two_mul_le','exponent_le_B','prefixExponent_spec','right_bounded_exponent_half','right_bounded_prefix_half','evol_right_diagonal_half'],
 module:['code_high','anchors','orb_bit','front_half_period_zero','front_half_period'],
 'Ruliology.CellularAutomata.Rule30PrefixClockGrowth':['edge_witness','prefix_period_edge_bound','prefix_exponent_lower','prefix_exponents_unbounded','two_sided_prefix_clock']}
checks={};allheads=[]
for index,(name,short) in enumerate(specs.items()):
    heads=[name+'.'+s for s in short];allheads+=heads
    cmd=[str(lake),'env',str(a.lean),'--run',str(project/'Check.lean'),name,'--claim','partial']
    for h in heads:cmd+=['--headline',h]
    log=f'check-{index}.log';run(cmd,log)
    c=json.loads(next(s for s in reversed((out/log).read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
    assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    checks[name]=c
types=out/'Types.lean';types.write_text('import '+module+'\nimport Ruliology.CellularAutomata.Rule30PrefixClockGrowth\n'+''.join('#check @'+h+'\n#print axioms '+h+'\n' for h in allheads),encoding='utf-8')
run([str(lake),'env',str(a.lean),str(types)],'Types.log')
for f in meta['files']:assert sha(root/f['path'])==f['sha256']
r={'passed':True,'official_pin':meta['pin'],'fresh_source_modules':26,'reused_objects':False,'whole_catalog_build':False,'checkers':checks,'owned_declarations':sum(c['replay']['constants'] for c in checks.values()),'headlines':len(allheads),'source_files':meta['files'],'source_warnings':b'warning:' in (out/'build.log').read_bytes(),'seconds':time.monotonic()-start}
(out/'RESULT.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'passed':True,'constants':r['owned_declarations'],'headlines':r['headlines'],'source_warnings':r['source_warnings'],'seconds':r['seconds']}))
