module
public import Rule30CubicPackedSemanticsV2
@[expose] public section
namespace Rule30CubicOrbitSemantics
open Rule30CubicCertificateData
open Rule30CubicPackedSemanticsV2
open Rule30ReaderCanonicalResearch
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

theorem packed_step (x : Nat) :
    singleStep (word x width)=word (stepPacked x) width := by
  apply List.ext_getElem
  · simp only [singleStep,change_length,word_length]
  · intro i hi hj
    have h : i<width := by simpa only [word_length] using hj
    rw [word_getElem (stepPacked x) width i h]
    have he := stepPacked_matches_rule x i h
    simpa [bget,List.getElem?_eq_getElem,hi,hj,word_getElem] using he

def packedIter (x : Nat) : Nat → Nat
  | 0 => x
  | n+1 => stepPacked (packedIter x n)

theorem packed_iter (x t : Nat) :
    iter (word x width) t=word (packedIter x t) width := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [iter,packedIter,ih,packed_step]

theorem packed_iter_step (x t : Nat) :
    packedIter (stepPacked x) t=packedIter x (t+1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [packedIter,ih]

theorem run_cycle (o : Orbit) (n q x : Nat) (hc : checkRun o q n x=true) :
    packedIter x n=o.initial := by
  induction n generalizing q x with
  | zero => simpa only [checkRun,packedIter,beq_iff_eq] using hc
  | succ n ih =>
    have h := hc
    simp only [checkRun,Nat.ble_eq_true_of_le (Nat.zero_le _),ite_true,
      Bool.and_eq_true] at h
    simpa only [packed_iter_step] using ih (q+1) (stepPacked x) h.2

theorem run_profile (o : Orbit) (n q x : Nat) (hc : checkRun o q n x=true) :
    ∀ t, t<n →
      (packedIter x t).testBit (width-1)=o.g.testBit (q+t) ∧
      ((packedIter x t).testBit (width-1) ||
        (packedIter x t).testBit (width-2))=o.r.testBit (q+t) := by
  induction n generalizing q x with
  | zero => intro t ht;omega
  | succ n ih =>
    have h := hc
    simp only [checkRun,Nat.ble_eq_true_of_le (Nat.zero_le _),ite_true,
      Bool.and_eq_true,beq_iff_eq] at h
    intro t ht
    cases t with
    | zero => simpa only [packedIter,Nat.add_zero] using h.1
    | succ t =>
      have hp := ih (q+1) (stepPacked x) h.2 t (by omega)
      simpa only [packed_iter_step,show q+1+t=q+(t+1) by omega] using hp

theorem checked_orbit_is_actual_cycle (o : Orbit) (hc : checkOrbit o=true) :
    Canonical (word o.initial width++[false]) ∧
    iter (word o.initial width) o.period=word o.initial width := by
  have h := hc
  simp only [checkOrbit,Bool.and_eq_true,decide_eq_true_eq] at h
  refine ⟨h.1.2,?_⟩
  rw [packed_iter,run_cycle o o.period 0 o.initial h.2]

end Rule30CubicOrbitSemantics
