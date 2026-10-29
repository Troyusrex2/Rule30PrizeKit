"""Replay frozen sources with Lean4.35 and a prepared, pinned Mathlib cache.
No downloads. --out must not exist. Does not reuse any owned .olean files.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,time
HERE=Path(__file__).resolve().parent
HEADS={
 'HankelSourceResearch':['integer_hankel8_null','fresh_source_cancels','rational_pivot_lifts',
  'alphabet_forces_third_border','even_two_step','odd_two_step','spaced_even','spaced_odd',
  'first_arrival','coincident_arrivals','cannot_separate_at_arrival'],
 'NewtonHankel':['det_hankel_transform_two','newton_row_succ','actual_sourceProduct',
  'transform_involutive','transform_even','transform_odd','sourceProduct_even',
  'sourceProduct_odd','newest_neighbor_still_masked'],
 'EndpointTransport':['fill_step','fill_right0','fill_right1','endpoint_rectangle',
  'endpoint_obstructs_separable','single_site_flux_trivial'],
 'EndpointCountermodel':['endpoint_complete','endpoint_complete_periodic_center',
  'endpoint_control_does_not_imply_seed_aperiodicity'],
 'ResetCountermodel':['reset0101_constant','evol_ether','resets_every_time_constant_center',
  'ether_is_not_left_finite','finite_prefix_reset_counterfamily'],
 'SmallIntegerWitness':['certificate_matches','witness_bits','shifted_integer_fresh_source_cancels']}

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--lean',type=Path,required=True)
    ap.add_argument('--mathlib-packages',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();lean=args.lean.resolve();pack=args.mathlib_packages.resolve()
    for name,h in json.loads((HERE/'INPUT-HASHES.json').read_text()).items():
        assert sha(HERE/name)==h,name
    pin='56a005855ea17e0b0958f73ec801ae140b0a1679'
    actual=subprocess.check_output(['git','-C',str(pack/'mathlib'),'rev-parse','HEAD'],text=True).strip()
    assert actual==pin,(actual,pin)
    paths=[p/'.lake/build/lib/lean' for p in pack.iterdir() if (p/'.lake/build/lib/lean').is_dir()]
    assert any(p.parts[-5]=='mathlib' for p in paths),paths
    out=args.out.resolve();out.mkdir(parents=True,exist_ok=False)
    src=out/'sources';shutil.copytree(HERE/'sources',src);shutil.copy2(HERE/'Check.lean',src/'Check.lean')
    logs=out/'logs';logs.mkdir()
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[src]+paths)),LEAN_NUM_THREADS='1')
    env.pop('LEAN_SRC_PATH',None)
    version=subprocess.check_output([str(lean),'--version'],text=True,env=env).strip()
    assert 'version 4.35.0,' in version,version
    def run(command,log):
        with (logs/log).open('wb') as f:
            r=subprocess.run([str(lean)]+list(map(str,command)),cwd=src,env=env,
                             stdout=f,stderr=subprocess.STDOUT,timeout=90)
        if r.returncode:
            print((logs/log).read_text(encoding='utf-8',errors='replace')[-5000:])
            r.check_returncode()
    start=time.monotonic()
    official=['Ruliology.CellularAutomata.Rule30Jen','Ruliology.CellularAutomata.Rule30Prize',
              'Ruliology.CellularAutomata.Rule30Realization']
    for module in official+list(HEADS):
        rel=Path(module.replace('.','/'))
        run(['-o',rel.with_suffix('.olean'),rel.with_suffix('.lean')],module+'.build.log')
        assert 'warning:' not in (logs/(module+'.build.log')).read_text(encoding='utf-8')
    checks={}
    for module,heads in HEADS.items():
        cmd=['--run','Check.lean',module,'--claim','partial']
        for h in heads:cmd+=['--headline',module+'.'+h]
        run(cmd,module+'.check.log')
        result=json.loads(next(x for x in reversed((logs/(module+'.check.log')).read_text().splitlines()) if x.startswith('{')))
        assert result['verdict']=='pass' and result['replay']['ok'] and not result['newAxioms']
        assert all(h['ok'] for h in result['headlines'])
        checks[module]={'constants':result['replay']['constants'],'headlines':len(result['headlines']),
                        'verdict':result['verdict'],'newAxioms':result['newAxioms']}
    result={'passed':True,'lean_version':version,'lean_sha256':sha(lean),'checker_sha256':sha(HERE/'Check.lean'),
      'official_pin':'932cf8dde039b89b1dcbe9636867bb1b2057fef0','mathlib_pin':pin,
      'fresh_official_sources':3,'fresh_owned_modules':len(HEADS),'reused_owned_objects':False,
      'cached_mathlib_dependencies':True,'cold_mathlib_build':False,'whole_catalog_build':False,
      'checks':checks,'partial_accepts_arbitrary_types':True,'prize_solution':False,
      'all_width_charge_classification_formalized':False,'seconds':time.monotonic()-start}
    (out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
