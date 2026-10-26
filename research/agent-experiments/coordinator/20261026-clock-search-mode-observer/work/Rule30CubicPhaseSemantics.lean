module
public import Rule30CubicCertificateChecked
public import Rule30ReaderObserverReductionResearch
@[expose] public section
namespace Rule30CubicPhaseSemantics
open Rule30CubicCertificateData
open Rule30CubicCertificateChecked
open Rule30CubicPackedSemanticsV2
open Rule30CubicOrbitSemantics
open Rule30ReaderCanonicalResearch
open Rule30ReaderObserverReductionResearch
set_option maxHeartbeats 4000000

theorem canonical_closed_check : (List.range 7).all
    (fun q => decide (∀ x : Bool, cnext q x<7))=true := by decide +kernel
theorem canonical_last_check : (List.range 7).all
    (fun q => decide (∀ x y : Bool, caccept (cnext q x)=caccept (cnext q y)))=true := by
  decide +kernel

theorem crun_bounded (xs : List Bool) (q : Nat) (hq : q<7) : crun q xs<7 := by
  induction xs generalizing q with
  | nil => exact hq
  | cons x xs ih =>
    exact ih (cnext q x) ((of_decide_eq_true (List.all_eq_true.mp
      canonical_closed_check q (List.mem_range.mpr hq))) x)

theorem crun_append_local (xs ys : List Bool) (q : Nat) :
    crun q (xs++ys)=crun (crun q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons x xs ih => exact ih (cnext q x)

theorem canonical_last_free (xs : List Bool) (x y : Bool) :
    Canonical (xs++[x]) ↔ Canonical (xs++[y]) := by
  have h := (of_decide_eq_true (List.all_eq_true.mp canonical_last_check
    (crun 0 xs) (List.mem_range.mpr (crun_bounded xs 0 (by decide))))) x y
  unfold Canonical
  simp only [crun_append_local,crun]
  rw [h]

theorem canonical_parent_phase (xs : List Bool) (hc : Canonical (xs++[false])) (t : Nat) :
    Canonical (iter xs t++[false]) := by
  obtain ⟨y,hy⟩ := iter_snoc xs false t
  have h := canonical_iter (xs++[false]) hc t
  rw [hy] at h
  exact (canonical_last_free (iter xs t) y false).mp h

theorem all_certificate_phases_canonical (o : Orbit) (ho : o∈orbits) (t : Nat) :
    Canonical (iter (word o.initial width) t++[false]) := by
  exact canonical_parent_phase _ (every_record_is_canonical_cycle o ho).1 t

theorem all_certificate_profiles_actual (o : Orbit) (ho : o∈orbits) (t : Nat)
    (ht : t<o.period) :
    bget (iter (word o.initial width) t) (width-1)=o.g.testBit t ∧
    (bget (iter (word o.initial width) t) (width-1) ||
      bget (iter (word o.initial width) t) (width-2))=o.r.testBit t := by
  have hc := List.all_eq_true.mp all_orbits_checked o ho
  simp only [checkOrbit,Bool.and_eq_true] at hc
  have h := run_profile o o.period 0 o.initial hc.2 t ht
  rw [packed_iter,word_bget _ _ _ (by decide +kernel),
    word_bget _ _ _ (by decide +kernel)]
  simpa only [Nat.zero_add] using h

end Rule30CubicPhaseSemantics
