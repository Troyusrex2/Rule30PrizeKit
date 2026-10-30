"""Portable Lean4.35 core replay of this research block. No network or SAT."""
from pathlib import Path
import argparse,subprocess,os,shutil,json,hashlib,datetime,time,sys
sys.stdout.reconfigure(encoding='utf-8')
ROOT=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--lean',default=shutil.which('lean'));args=ap.parse_args();assert args.lean
lean=str(Path(args.lean).resolve());version=subprocess.check_output([lean,'--version'],text=True);assert '4.35.0' in version
start=time.monotonic();stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
P=ROOT/('build-'+stamp);assert not P.exists();shutil.copytree(ROOT/'proofs',P)
assert P.resolve().is_relative_to(ROOT.resolve())
env=dict(os.environ,LEAN_PATH=str(P),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
base='Ruliology/CellularAutomata/'
order=[base+x for x in ['Rule30Jen','Rule30Prize','Rule30Realization','Rule30FrozenRuler']]
order+=['CanonicalDecoration','LeakDescent','ReturnActions','ReturnSections','MaskDynamics','QuietClock',
 'WordBoundary','TemporalAncestry','TwoClockAlias','RelativeRank','RankEscape','ControlledBudget','MemorySeparation',
 base+'Rule30EdgeClock',base+'Rule30DefectClockBudget']
def run(cmd,label):
    with (P/(label+'.log')).open('wb') as f:p=subprocess.run(cmd,cwd=P,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=90)
    out=(P/(label+'.log')).read_text(encoding='utf-8');assert p.returncode==0,(label,out[-3000:])
    if 'warning:' in out:assert label.endswith('_check') and out.count('warning:')==1 and '`Lean.Environment.replay` has been deprecated' in out,(label,out[-3000:])
    return out
for module in order:
    f=P/(module+'.lean');run([lean,'-o',str(f.with_suffix('.olean')),str(f)],Path(module).name)
for f in sorted((ROOT/'guards').glob('*.lean')):
    shutil.copyfile(f,P/f.name);run([lean,str(P/f.name)],f.stem)
expected='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256((P/'Check.lean').read_bytes()).hexdigest()==expected
heads={
 'Ruliology.CellularAutomata.Rule30DefectClockBudget':['rank_certificate','measure_step','black_within','four_layer_escape','recurrent_four_layer_escape'],
 'WordBoundary':['memory_equal_all','shared_words_confine_at_cut','reflection_of_word_injective'],
 'TemporalAncestry':['no_ACC_from','word_end_obstruction','all_bad_powers_unreachable','white_pair_rise_falls'],
 'TwoClockAlias':['actual_control_step','two_ancestor_recurrences','controlled_confined','different_forever','actual_recurrent_black','boundary_word_swaps_prefixes','square_word_alias'],
 'ControlledBudget':['no_four_digit_trap','five_digit_recurrent_trap','no_black_tick_budget_for_five_digit_example'],
 'MemorySeparation':['exact_tail_and_one','source_collision_separation']}
results={}
for module,names in heads.items():
    cmd=[lean,'--run',str(P/'Check.lean'),module,'--claim','partial']
    for name in names:cmd+=['--headline',module+'.'+name]
    out=run(cmd,module.split('.')[-1]+'_check')
    check=json.loads(next(x for x in reversed(out.splitlines()) if x.startswith('{')))
    assert check['verdict']=='pass' and check['replay']['ok'] and not check['newAxioms']
    assert all(h['ok'] and h['typeMatches'] for h in check['headlines'])
    results[module]=dict(declarations=check['replay']['constants'],headlines=len(names),replay=True,new_axioms=[])
    print(json.dumps(dict(module=module,passed=True,**results[module])),flush=True)
receipt=dict(passed=True,lean_version=version.strip(),checker_sha256=expected,modules=results,
    build_modules=len(order),headlines=sum(v['headlines'] for v in results.values()),seconds=time.monotonic()-start,
    new_axioms=[],proof_source_warnings=False,checker_warning='Known unchanged Environment.replay deprecation warning.',
    full_catalog_build=False,prize_solved=False)
(ROOT/'REPLAY.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(passed=True,modules=len(results),headlines=receipt['headlines'],seconds=receipt['seconds'])))
