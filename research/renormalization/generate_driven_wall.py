"""Generate a finite invariant certificate; Lean independently checks all cases.

The search and this generator are untrusted. The generated Good-block proofs
use ordinary decide, and the unchanged checker must replay them all.
"""
import hashlib
import json
from pathlib import Path

import numpy as np

from right_prefix_safety import double_step

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]


def main():
    width=16; values=np.arange(1 << width,dtype=np.uint64);mask=(1 << width)-1
    v=values.copy(); bad=np.zeros(len(v),dtype=bool)
    for j in range(1,5):
        v=double_step(v)
        if j in (2,4):bad |= ((values&v&1)!=0)
    alive=~bad
    successors=[(double_step(values|(tail << width))&mask).astype(np.uint32) for tail in range(4)]
    rounds=0
    while True:
        nxt=alive.copy()
        for ix in successors:nxt &= alive[ix]
        rounds+=1
        if np.array_equal(nxt,alive):break
        alive=nxt
    assert all(np.all(alive[ix[alive]]) for ix in successors)
    v=values.copy();window=np.zeros(len(v),dtype=np.uint64)
    for j in range(6):window|=(v&1) << j;v=double_step(v)
    allowed={2,4,8,9,16,18,33,34,36}
    assert set(np.unique(window[alive]).tolist()) <= allowed
    a=1
    for _ in range(146):a=double_step(a)
    assert alive[a&mask]
    packed=np.packbits(alive,bitorder='little').tobytes()
    number=int.from_bytes(packed,'little')
    lines=['module','',
      'public import Ruliology.CellularAutomata.Rule30DrivenPrefixResearch','',
      '/-! Untrusted generated wall data; every membership, observation and',
      'transition case is checked below by ordinary kernel reduction. -/','',
      '@[expose] public section','',
      'namespace Ruliology.CellularAutomata.Rule30Certificates.DrivenEmptyWall','',
      'open Rule30DrivenPrefixResearch','',
      f'def wallMask : Nat := 0x{number:x}','',
      'def wall (q : Nat) : Bool := wallMask.testBit (q % 65536)','',
      'def Good (q : Nat) : Prop := wall q=true → Observe q ∧ wall (double q)=true','',
      'instance (q : Nat) : Decidable (Good q) := inferInstanceAs',
      '  (Decidable (wall q=true → Observe q ∧ wall (double q)=true))','',
      'def checkBlock (base : Nat) : Bool :=',
      '  (List.range 1024).all (fun j => decide (Good (base+j)))','',
      'set_option maxRecDepth 1000000','set_option maxHeartbeats 0','']
    for block in range(256):
        lines.append(f'theorem block{block} : checkBlock {1024*block}=true := by decide')
    lines+=['','theorem all_blocks : ∀ n, n<256 → checkBlock (1024*n)=true']
    for block in range(256):lines.append(f'  | {block},_ => block{block}')
    lines += ['  | n+256,h => by omega','',
      'theorem good_all (q : Nat) (hq : q<262144) : Good q := by',
      '  have hb := all_blocks (q/1024) (by omega)',
      '  have he := (List.all_eq_true.mp hb) (q%1024) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))',
      '  have hh : 1024*(q/1024)+q%1024=q := by omega',
      '  rw [hh] at he',
      '  exact of_decide_eq_true he','',
      'theorem entry : wall (white 146)=true := by decide','',
      'end Ruliology.CellularAutomata.Rule30Certificates.DrivenEmptyWall','']
    target=ROOT/'lean/Ruliology/CellularAutomata/Rule30Certificates/DrivenEmptyWall.lean'
    target.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
    report={'untrusted_generator':True,'Lean_verified':False,'width':width,
            'safe_states':int(alive.sum()),'rounds':rounds,'entry_white_cycle':146,
            'entry_time':293,'entry_prefix':a&mask,'closed_under_all_tail_completions':True,
            'allowed_six_gate_windows':sorted(allowed),'exhaustive_cases':262144,
            'packed_mask_sha256':hashlib.sha256(packed).hexdigest(),
            'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
    (HERE/'driven-wall-generation.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__':main()
