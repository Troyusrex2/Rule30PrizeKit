"""Portable core-Lean replay; no private paths or network required."""
from pathlib import Path
import argparse,subprocess,os,shutil,json,hashlib,datetime,time,sys
sys.stdout.reconfigure(encoding='utf-8')
ROOT=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--lean',default=shutil.which('lean'));args=ap.parse_args()
assert args.lean,'Pass --lean path/to/Lean4.35.0/lean.exe'
lean=str(Path(args.lean).resolve());version=subprocess.check_output([lean,'--version'],text=True)
assert '4.35.0' in version,version
start=time.monotonic();stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
P=ROOT/('build-'+stamp);assert not P.exists();shutil.copytree(ROOT/'proofs',P)
assert P.resolve().is_relative_to(ROOT.resolve())
env=dict(os.environ,LEAN_PATH=str(P),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
base='Ruliology/CellularAutomata/'
order=[base+n for n in ['Rule30Jen','Rule30Prize','Rule30Realization','Rule30FrozenRuler']]
order+=['CanonicalDecoration','LeakDescent','ReturnActions','ReturnSections','ReachabilityBarrier',
        'MaskDynamics','QuietClock','TwoLayerEscape','ClockDelay','WindowBarrier','ControlledAlias',base+'Rule30EdgeClock']
def run(cmd,name):
    with (P/(name+'.log')).open('wb') as f:
        p=subprocess.run(cmd,cwd=P,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=90)
    out=(P/(name+'.log')).read_text(encoding='utf-8')
    assert p.returncode==0,(name,out[-4000:])
    if 'warning:' in out:
        assert name.endswith('_check') and out.count('warning:')==1 and \
            '`Lean.Environment.replay` has been deprecated' in out,(name,out[-4000:])
    return out
for name in order:
    src=P/(name+'.lean');run([lean,'-o',str(src.with_suffix('.olean')),str(src)],Path(name).name)
for src in sorted((ROOT/'guards').glob('*.lean')):
    shutil.copyfile(src,P/src.name);run([lean,str(P/src.name)],src.stem)
expected='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256((P/'Check.lean').read_bytes()).hexdigest()==expected
heads={
 'Ruliology.CellularAutomata.Rule30EdgeClock':['flip_bound','flip_bound_from','seed_at_bound','higher_excitation','recurrent_excitation','two_layer_escape','recurrent_two_layer_escape'],
 'ClockDelay':['arbitrary_delay','no_distance_only_bound','first_difference','finite_pair','parentless','sharp_two_layer'],
 'WindowBarrier':['no_ranking','no_two_step_ranking'],
 'TwoLayerEscape':['three_rows_force_white','two_layer_escape'],
 'ControlledAlias':['act_is_controlled','ancestor_compatible','controlled_confined','different_forever','recurrent_black_control']}
results={}
for module,names in heads.items():
    cmd=[lean,'--run',str(P/'Check.lean'),module,'--claim','partial']
    for n in names:cmd+=['--headline',module+'.'+n]
    out=run(cmd,module.split('.')[-1]+'_check')
    check=json.loads(next(x for x in reversed(out.splitlines()) if x.startswith('{')))
    assert check['verdict']=='pass' and check['replay']['ok'] and not check['newAxioms']
    assert all(h['ok'] and h['typeMatches'] for h in check['headlines'])
    results[module]=dict(declarations=check['replay']['constants'],headlines=len(names),replay=True,new_axioms=[])
    print(json.dumps(dict(module=module,passed=True,**results[module])),flush=True)
subprocess.run([sys.executable,str(ROOT/'verify_certificates.py')],cwd=ROOT,check=True,timeout=30)
receipt=dict(passed=True,lean_version=version.strip(),checker_sha256=expected,modules=results,
    built_modules=len(order),seconds=time.monotonic()-start,prize_solved=False,full_catalog_build=False,
    source_warnings=False,checker_warning='Unmodified Check.lean uses deprecated Lean.Environment.replay; accepted only this known checker warning.')
(ROOT/'REPLAY.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(passed=True,modules=len(results),headlines=sum(v['headlines'] for v in results.values()),seconds=receipt['seconds'])))
