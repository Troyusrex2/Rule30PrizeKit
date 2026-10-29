from pathlib import Path
from pivot_probe import simulate
ROOT=Path(__file__).resolve().parent
rows=simulate(40,42)
tables=['['+','.join('true' if (r>>(42+p))&1 else 'false' for p in range(-40,41))+']' for r in rows]
header='''module
public import HankelSourceResearch
/-! Exact shifted integer-border witness, using a Boolean spacetime certificate.
All certificate transitions are checked in the kernel; no native_decide. -/
@[expose] public section
namespace SmallIntegerWitness
open Ruliology.CellularAutomata Rule30Jen Rule30Prize HankelSourceResearch
def certificate : List (List Bool) :=
  ['''+',\n   '.join(tables)+''']
def table (t k : Nat) : Bool := (certificate.getD t []).getD k false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem certificate_base : ∀ i : Fin 81, table 0 i.val=decide (i.val=40) := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem certificate_steps : ∀ t : Fin 40, ∀ i : Fin 79,
    table (t.val+1) (i.val+1)=rule (table t.val i.val)
      (table t.val (i.val+1)) (table t.val (i.val+2)) := by decide

theorem certificate_matches : ∀ t : Nat, t≤40 → ∀ k : Nat,
    t≤k → k+t≤80 → cell t ((k:Int)-40)=table t k
  | 0,ht,k,hk,hkt => by
    change decide ((k:Int)-40=0)=table 0 k
    have he : ((k:Int)-40=0) ↔ k=40 := by omega
    simpa only [he] using (certificate_base ⟨k,by omega⟩).symm
  | t+1,ht,k,hk,hkt => by
    change rule (cell t ((k:Int)-40-1)) (cell t ((k:Int)-40))
      (cell t ((k:Int)-40+1))=table (t+1) k
    have hl : cell t ((k:Int)-40-1)=table t (k-1) := by
      rw [←show ((k-1:Nat):Int)-40=(k:Int)-40-1 by omega]
      exact certificate_matches t (by omega) (k-1) (by omega) (by omega)
    have hc := certificate_matches t (by omega) k (by omega) (by omega)
    have hr : cell t ((k:Int)-40+1)=table t (k+1) := by
      rw [←show ((k+1:Nat):Int)-40=(k:Int)-40+1 by omega]
      exact certificate_matches t (by omega) (k+1) (by omega) (by omega)
    rw [hl,hc,hr]
    have hs := certificate_steps ⟨t,by omega⟩ ⟨k-1,by omega⟩
    simpa only [show k-1+1=k by omega,show k-1+2=k+1 by omega] using hs.symm

theorem witness_bits : center 36=false ∧ center 37=true ∧ center 38=false ∧
    center 39=true ∧ center 40=false ∧ cell 39 1=true := by
  have h (t : Nat) (ht : t≤40) : center t=table t 40 := by
    simpa [center] using certificate_matches t ht 40 (by omega) (by omega)
  have hr : cell 39 1=table 39 41 := by
    exact certificate_matches 39 (by decide) 41 (by decide) (by decide)
  exact ⟨(h 36 (by decide)).trans (by decide),(h 37 (by decide)).trans (by decide),
    (h 38 (by decide)).trans (by decide),(h 39 (by decide)).trans (by decide),
    (h 40 (by decide)).trans (by decide),hr.trans (by decide)⟩

theorem shifted_integer_fresh_source_cancels :
    det2 (zbit (center 36)) (zbit (center 37)) (zbit (center 37)) (zbit (center 38)) = -1 ∧
    (center 39 && cell 39 1)=true ∧
    det3 (zbit (center 36)) (zbit (center 37)) (zbit (center 38))
      (zbit (center 37)) (zbit (center 38)) (zbit (center 39))
      (zbit (center 38)) (zbit (center 39)) (zbit (center 40))=0 := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := witness_bits
  rw [ha,hb,hc,hd,he,hf]
  decide
end SmallIntegerWitness
'''
(ROOT/'math/SmallIntegerWitness.lean').write_text(header,encoding='utf-8',newline='\n')
print('Boolean_certificate_rows',len(rows),'columns',81)
