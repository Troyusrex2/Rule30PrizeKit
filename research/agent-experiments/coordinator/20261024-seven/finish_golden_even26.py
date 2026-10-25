"""Aggregate only exact-source passing partition reports, then replay the bridge."""
import hashlib,json,subprocess,sys
from core import HERE

def plan():
    return [(f'Rule30GoldenEven26Chunk{b:02d}Research',range(8*b,8*b+8)) for b in range(3)]+[
        (f'Rule30GoldenEven26Part{b:02d}Research',range(4*b,4*b+4)) for b in range(6,16)]

def main():
    modules=plan();lookup={}
    for m,cases in modules:
        r=json.loads((HERE/'golden-even26-evidence'/m/'report.json').read_text(encoding='utf-8'))
        assert r['source_sha256']==hashlib.sha256((HERE/(m+'.lean')).read_bytes()).hexdigest()
        assert r['check']['verdict']=='pass' and r['check']['replay']['ok'] and not r['check']['newAxioms']
        assert all(h['ok'] for h in r['check']['headlines'])
        for c in cases:lookup[c]=m+'.check_'+str(c)
    assert sorted(lookup)==list(range(64))
    name='Rule30GoldenEvenWidth26Research'
    text=''.join('import '+m+'\n' for m,_ in modules)
    text+='import Rule30GoldenHistoryResearch\nimport Rule30GoldenCoupledResearch\n\n'
    text+='namespace '+name+'\nopen Rule30GoldenEvenSupportResearch\n\n'
    text+='theorem checks (c : Nat) (hc : c < 64) : check 20 c 61 = true := by\n'
    text+='  rcases (show '+' ∨ '.join('c='+str(c) for c in range(64))+' by omega) with\n'
    text+='    '+' | '.join('rfl' for _ in range(64))+'\n'
    for c in range(64):text+='  · exact '+lookup[c]+'\n'
    text+='''
theorem noGoldenEvenWidth26 : NoGoldenEvenWidth 26 := by
  apply no_golden_even_width_of_checks 26 20 61 (by omega)
  intro c hc
  exact checks c (by simpa using hc)

theorem noGoldenEvenWidth_le26 {M : Nat} (hM : M ≤ 26) : NoGoldenEvenWidth M := by
  intro s hs
  apply noGoldenEvenWidth26 s
  intro d hd
  exact hs d (by omega)

theorem not_alternating_of_even_width26 (T : Nat)
    (he : ∀ d, 26 ≤ d → Ruliology.CellularAutomata.Rule30ZeroBoundary.leftRow T (2*d+2) = false) :
    ¬ ∀ k, Ruliology.CellularAutomata.Rule30Jen.cell (T+2*k) 0 = true ∧
      Ruliology.CellularAutomata.Rule30Jen.cell (T+2*k+1) 0 = false :=
  Rule30GoldenHistoryResearch.not_alternating_of_even_width noGoldenEvenWidth26 he

theorem psi_even_escape26 (R : Nat → Bool) :
    ∃ d, 26 ≤ d ∧ Ruliology.CellularAutomata.Rule30PeriodTwoSideways.Psi R (2*d+2) = true :=
  Rule30GoldenCoupledResearch.psi_even_escape noGoldenEvenWidth26 R

'''
    text+='end '+name+'\n'
    target=HERE/(name+'.lean')
    if target.exists() and target.read_text(encoding='utf-8')!=text:raise RuntimeError('Different owned aggregation source')
    target.write_text(text,encoding='utf-8',newline='\n')
    subprocess.run([sys.executable,str(HERE/'verify_research_module.py'),'--module',name,
        '--headlines','checks','noGoldenEvenWidth26','noGoldenEvenWidth_le26',
        'not_alternating_of_even_width26','psi_even_escape26','--output',
        str(HERE/'golden-even26-aggregation-evidence')],cwd=HERE,check=True)

if __name__=='__main__':main()
