"""Emit a kernel-checkable stronger wall and its eight-gate-word observations."""
import hashlib
import json
from pathlib import Path

from empty_gate_controller import make_controller
from right_prefix_safety import double_step

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]


def main():
    controller=make_controller(7);states=controller['core_states'];allowed=controller['transition_words']
    packed=sum(1<<q for q in states);state_set=set(states)
    assert len(states)==740 and controller['entry_cycle']==155
    assert all((double_step(q|(tail<<16))&65535) in state_set for q in states for tail in range(4))
    for q in states:
        v=q;word=0
        for j in range(8):word|=(v&1)<<j;v=double_step(v)
        assert word in allowed and word&73!=73
    a=1
    for _ in range(155):a=double_step(a)
    assert (a&65535) in state_set
    wordexpr=' ||| '.join(f'(((iterate a {j}).testBit 0).toNat <<< {j})' for j in range(8))
    observation=('((iterate a 0).testBit 0 && (iterate a 3).testBit 0 && (iterate a 6).testBit 0)=false '
                 f'∧ word8 a ∈ {allowed}')
    lines=['module','','public import Ruliology.CellularAutomata.Rule30DrivenPrefixResearch','',
      '/-! Generated finite core data. Search and extraction are untrusted; all cases use ordinary decide. -/','',
      '@[expose] public section','','namespace Ruliology.CellularAutomata.Rule30Certificates.DrivenEmptyCore','',
      'open Rule30DrivenPrefixResearch','',f'def wallMask : Nat := 0x{packed:x}',
      'def wall (q : Nat) : Bool := wallMask.testBit (q%65536)','',
      f'def word8 (a : Nat) : Nat := {wordexpr}','',
      f'def Observe (a : Nat) : Prop := {observation}','',
      f'instance (a : Nat) : Decidable (Observe a) := inferInstanceAs (Decidable ({observation}))','',
      'theorem observe_trim (a : Nat) : Observe (a%2^18) ↔ Observe a := by',
      '  simp only [Observe,word8]',
      '  rw ['+', '.join(f'iterate_mod_bit a 18 {j} 0 (by decide)' for j in range(8))+']','',
      'def Good (q : Nat) : Prop := wall q=true → Observe q ∧ wall (double q)=true',
      'instance (q : Nat) : Decidable (Good q) := inferInstanceAs',
      '  (Decidable (wall q=true → Observe q ∧ wall (double q)=true))','',
      'def checkBlock (base : Nat) : Bool := (List.range 1024).all (fun j => decide (Good (base+j)))','',
      'set_option maxRecDepth 1000000','set_option maxHeartbeats 0','']
    for i in range(256):lines.append(f'theorem block{i} : checkBlock {i*1024}=true := by decide')
    lines+=['','theorem all_blocks : ∀ n, n<256 → checkBlock (1024*n)=true']
    for i in range(256):lines.append(f'  | {i},_ => block{i}')
    lines+=['  | n+256,h => by omega','','theorem good_all (q : Nat) (hq : q<262144) : Good q := by',
      '  have hb := all_blocks (q/1024) (by omega)',
      '  have he := (List.all_eq_true.mp hb) (q%1024) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))',
      '  have hh : 1024*(q/1024)+q%1024=q := by omega','  rw [hh] at he','  exact of_decide_eq_true he','',
      'theorem entry : wall (white 155)=true := by decide','',
      'end Ruliology.CellularAutomata.Rule30Certificates.DrivenEmptyCore','']
    target=ROOT/'lean/Ruliology/CellularAutomata/Rule30Certificates/DrivenEmptyCore.lean'
    target.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
    report={'untrusted_generator':True,'Lean_verified':False,'core_states':len(states),
            'entry_cycle':155,'physical_time':311,'entry_prefix':a&65535,'allowed_word8':allowed,
            'all_tail_transitions':4*len(states),'all_eighteen_bit_cases':262144,
            'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
    (HERE/'empty-core-generation.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__':main()
