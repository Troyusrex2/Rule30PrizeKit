"""Fresh-source replay. Python3, official Lean4.35.0; no downloads/Mathlib."""
from pathlib import Path
import argparse,json,os,subprocess,time,hashlib,shutil

HERE=Path(__file__).resolve().parent
HEADS=['driven_eq_of_mask','falling_transport','effective_falling_transport',
       'falling_of_transport','transport_iff_falling','consistent_transport',
       'consistency_iff','actual_consistent','tail_both_values',
       'problem1_of_periodic_mask_exclusion']

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--lean',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True);args=parser.parse_args()
    lean=args.lean.resolve();lake=lean.with_name('lake.exe' if lean.suffix=='.exe' else 'lake')
    out=args.out.resolve();out.mkdir(parents=True,exist_ok=False)
    inputs=json.loads((HERE/'OFFICIAL-INPUTS.json').read_text())
    assert sha(HERE/'Check.lean')==inputs['checker_sha256']
    for name,h in inputs['modules'].items():
        assert sha(HERE/'sources'/(name.replace('.','/')+'.lean'))==h
    manifest=HERE/'SOURCE-HASHES.json'
    for name,h in json.loads(manifest.read_text()).items():assert sha(HERE/name)==h,name
    shutil.copytree(HERE/'sources',out,dirs_exist_ok=True);shutil.copy2(HERE/'Check.lean',out/'Check.lean')
    env=dict(os.environ,PATH=str(lean.parent)+os.pathsep+os.environ.get('PATH',''),LEAN_NUM_THREADS='1')
    env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
    def run(command,log):
        with (out/log).open('wb') as f:
            r=subprocess.run(list(map(str,command)),cwd=out,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=180)
        if r.returncode:
            print((out/log).read_text(encoding='utf-8',errors='replace')[-4500:]);r.check_returncode()
    start=time.monotonic()
    version=subprocess.check_output([str(lean),'--version'],env=env,text=True).strip()
    assert 'version 4.35.0,' in version,version
    run([lake,'build','MaskedTransport'],'build.log')
    cmd=[lake,'env',lean,'--run',out/'Check.lean','MaskedTransport','--claim','partial']
    for name in HEADS:cmd+=['--headline','MaskedTransport.'+name]
    run(cmd,'check.log')
    check=json.loads(next(s for s in reversed((out/'check.log').read_text().splitlines()) if s.startswith('{')))
    assert check['verdict']=='pass' and check['replay']['ok'] and not check['newAxioms']
    assert all(h['ok'] for h in check['headlines'])
    (out/'Types.lean').write_text('import MaskedTransport\n'+''.join(
        '#check @MaskedTransport.'+h+'\n#print axioms MaskedTransport.'+h+'\n' for h in HEADS),encoding='utf-8')
    run([lake,'env',lean,out/'Types.lean'],'Types.log')
    guard='''import MaskedTransport
open Ruliology.CellularAutomata Rule30DrivenLeft
example (c : Nat → Bool) (s : Int → Bool) :
    (∀ t p, p<0 → L c s t p=L (MaskedTransport.effective c) s t p) ↔
      MaskedTransport.FallingPins c s := MaskedTransport.transport_iff_falling c s
example : MaskedTransport.PeriodicMaskExclusion → Rule30Prize.Problem1 :=
  MaskedTransport.problem1_of_periodic_mask_exclusion
'''
    (out/'TypeGuard.lean').write_text(guard,encoding='utf-8')
    run([lake,'env',lean,out/'TypeGuard.lean'],'TypeGuard.log')
    warnings='warning:' in (out/'build.log').read_text(encoding='utf-8')
    assert not warnings
    result={'passed':True,'official_pin':inputs['pin'],'official_source_hashes':inputs['modules'],
            'lean_version':version,'lean_binary_sha256':sha(lean),'checker_sha256':sha(HERE/'Check.lean'),
            'fresh_source_modules':5,'owned_modules':1,'reused_owned_objects':False,
            'whole_catalog_build':False,'constants':check['replay']['constants'],
            'headlines':len(check['headlines']),'source_warnings':warnings,
            'source_sha256':sha(out/'MaskedTransport.lean'),'check':check,
            'partial_check_accepts_arbitrary_theorem_types':True,'explicit_type_guards_passed':True,
            'open_exclusion_hypothesis_proved':False,'prize_solution':False,
            'seconds':time.monotonic()-start}
    (out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:result[k] for k in ['passed','constants','headlines','fresh_source_modules','seconds','prize_solution']},indent=2))

if __name__=='__main__':main()
