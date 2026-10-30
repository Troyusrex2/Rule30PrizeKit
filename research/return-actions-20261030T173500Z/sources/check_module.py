from pathlib import Path
import os,subprocess,time,json,hashlib,shutil,sys
sys.stdout.reconfigure(encoding='utf-8')
R=Path(__file__).resolve().parent;P=R/'project';module=sys.argv[1]
config={
 'ReturnSections':('SectionsGuard',['act_A','return_action','rigidity_iff_all_return_words','fixed_prefix_iff','double_even','double_odd','distinct_children']),
 'ReachabilityBarrier':('BarrierGuard',['bad_unreachable','bad_root_swaps','bad_cyclic_legal','bad_square_fixed_left','bad_square_fixed_right','bad_square_merges','bad_prefixes_distinct']),
 'MaskDynamics':('MaskGuard',['stall_turns_white','two_step_escape','different_gate_has_trapped_pair'])}
guard,heads=config[module];start=time.monotonic()
lean='D:/MWB/Rule30/toolchain/lean-4.35.0-windows/bin/lean.exe'
env=dict(os.environ,LEAN_PATH=str(P),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
shutil.copyfile(R/(guard+'.lean'),P/(guard+'.lean'))
def run(args,log):
    with (R/log).open('wb') as f:r=subprocess.run([lean]+list(map(str,args)),cwd=P,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=60)
    if r.returncode:print((R/log).read_text(encoding='utf-8')[-4000:]);raise SystemExit(r.returncode)
run(['-o',P/(guard+'.olean'),P/(guard+'.lean')],module+'_guard.log')
args=['--run',P/'Check.lean',module,'--claim','partial']
for head in heads:args+=['--headline',module+'.'+head]
run(args,module+'_checker.log')
result=json.loads(next(s for s in reversed((R/(module+'_checker.log')).read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
assert result['verdict']=='pass' and result['replay']['ok'] and not result['newAxioms']
assert all(h['ok'] and h['typeMatches'] for h in result['headlines'])
out=dict(module=module,passed=True,checker=result,seconds=time.monotonic()-start,
    checker_sha256=hashlib.sha256((P/'Check.lean').read_bytes()).hexdigest(),
    source_sha256=hashlib.sha256((R/(module+'.lean')).read_bytes()).hexdigest(),
    source_warnings='warning:' in (R/(module+'.log')).read_text(encoding='utf-8'),prize_solved=False)
(R/(module+'_CHECK.json')).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(module=module,passed=True,replay=result['replay'],headlines=len(heads),new_axioms=result['newAxioms'])))
