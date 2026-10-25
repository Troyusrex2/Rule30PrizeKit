import Rule30TailClassesResearch

namespace Rule30DelayedDefectResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30TailClassesResearch

def columns : List (List Bool) := [
  [false, false, false, false, false, false, false, false, false, false, false, false],
  [true, false, true, true, true, true, true, true, true, false, true, true],
  [true, true, false, false, false, false, false, false, true, true, false, false],
  [false, true, true, true, true, true, true, false, false, true, true, false],
  [false, false, false, false, false, false, true, false, false, false, true, false],
  [false, true, true, true, true, false, true, false, false, false, true, false],
  [true, false, false, false, true, true, true, false, false, true, true, false],
  [true, true, true, false, false, false, true, false, true, false, true, false],
  [false, false, true, false, true, false, true, true, true, false, true, true],
  [true, false, true, true, true, true, false, false, true, true, false, false],
  [true, true, false, false, false, true, true, false, false, true, true, false],
  [false, true, true, true, false, false, true, false, false, false, true, false],
  [false, false, false, true, false, false, true, false, false, false, true, false],
  [false, true, false, true, false, true, true, false, false, true, true, false],
  [true, true, true, true, true, false, true, false, true, false, true, false],
  [false, false, false, false, true, false, true, true, true, false, true, true],
  [true, true, true, false, true, true, false, false, true, true, false, false],
  [false, false, true, true, false, true, true, false, false, true, true, false],
  [true, false, false, true, false, false, true, false, false, false, true, false],
  [true, false, false, true, false, false, true, false, false, false, true, false],
  [true, false, true, true, false, true, true, false, false, true, true, false],
  [true, true, false, true, true, false, true, false, true, false, true, false],
  [false, true, false, false, true, false, true, true, true, false, true, true],
  [false, true, false, false, true, true, false, false, true, true, false, false],
  [true, true, false, true, false, true, true, false, false, true, true, false],
  [false, true, true, true, false, false, true, false, false, false, true, false]
]
def timeAt (t : Nat) := if t<8 then t else 8+(t-8)%4
def timeNext (t : Nat) := if t=11 then 8 else t+1
def spaceAt (d : Nat) := if d<12 then d else 12+(d-12)%14
def spaceNext (d : Nat) := if d=25 then 12 else d+1
def raw (d t : Nat) := (columns.getD d []).getD t false
def model (d t : Nat) := raw (spaceAt d) (timeAt t)
def base (t : Nat) := model 1 t
def pure (t : Nat) := decide (t%4≠1)

theorem timeAt_lt (t : Nat) : timeAt t<12 := by unfold timeAt; split <;> omega
theorem spaceAt_lt (d : Nat) : spaceAt d<26 := by unfold spaceAt; split <;> omega
theorem timeAt_succ (t : Nat) : timeAt (t+1)=timeNext (timeAt t) := by
  unfold timeAt timeNext
  split <;> split <;> split <;> omega
theorem spaceAt_succ (d : Nat) : spaceAt (d+1)=spaceNext (spaceAt d) := by
  unfold spaceAt spaceNext
  split <;> split <;> split <;> omega

theorem table_rule : ∀ d, d<26 → ∀ t, t<12 →
    raw (spaceNext (spaceNext d)) t =
      xor (raw (spaceNext d) (timeNext t)) (raw (spaceNext d) t || raw d t) := by
  have checked : (List.range 26).all (fun d => (List.range 12).all fun t =>
    raw (spaceNext (spaceNext d)) t ==
      xor (raw (spaceNext d) (timeNext t)) (raw (spaceNext d) t || raw d t)) = true := by decide
  intro d hd t ht
  exact beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp checked d (List.mem_range.mpr hd)) t (List.mem_range.mpr ht))

theorem model_rule (d t : Nat) : model (d+2) t =
    xor (model (d+1) (t+1)) (model (d+1) t || model d t) := by
  unfold model
  rw [show d+2=(d+1)+1 by omega,spaceAt_succ,spaceAt_succ,timeAt_succ]
  exact table_rule _ (spaceAt_lt d) _ (timeAt_lt t)

theorem model_zero (t : Nat) : model 0 t=false := by
  have h : ∀ t, t<12 → raw 0 t=false := by decide
  exact h _ (timeAt_lt t)

theorem model_eq_recon : ∀ d t, model d t=recon base d t := by
  have key : ∀ d, (∀ t, model d t=recon base d t) ∧
      (∀ t, model (d+1) t=recon base (d+1) t) := by
    intro d
    induction d with
    | zero => exact ⟨fun t => model_zero t,fun t => rfl⟩
    | succ d ih =>
      refine ⟨ih.2,fun t => ?_⟩
      rw [show d+1+1=d+2 by omega,model_rule,recon_two,ih.2,ih.2,ih.1]
  exact fun d t => (key d).1 t

theorem base_tail (t : Nat) (ht : 8≤t) : base t=pure t := by
  have h : ∀ q, q<4 → raw 1 (8+q)=decide (q≠1) := by decide
  unfold base model
  rw [show spaceAt 1=1 by decide,show timeAt t=8+t%4 by unfold timeAt; split <;> omega]
  simpa [pure] using h (t%4) (by omega)

theorem base_shift_eight : (fun t => base (t+8))=pure := by
  funext t
  rw [base_tail _ (by omega)]
  have hm : (t+8)%4=t%4 := by omega
  simp [pure,hm]

theorem base_formula (t : Nat) : base t=if t=5 then true else pure t := by
  by_cases ht : t<8
  · have h : ∀ t, t<8 → base t=if t=5 then true else pure t := by decide
    exact h t ht
  · rw [base_tail t (by omega),ite_eq_right (by omega)]

theorem pure_not_tail_base : ¬TailEq (fun d => recon pure d 0) (fun d => recon base d 0) := by
  rintro ⟨D,hD⟩
  let d := 14*D+15
  have hd : D≤d := by dsimp [d]; omega
  have hs : spaceAt d=15 := by unfold spaceAt; dsimp [d]; split <;> omega
  have hbase : recon base d 0=false := by
    rw [←model_eq_recon]
    unfold model
    rw [hs]
    decide
  have hpure : recon pure d 0=true := by
    have he : recon base d (0+8)=recon pure d 0 := by
      rw [recon_shift,base_shift_eight]
    rw [←he,←model_eq_recon]
    unfold model
    rw [hs]
    decide
  have h := hD d hd
  change recon pure d 0=recon base d 0 at h
  rw [hpure,hbase] at h
  exact Bool.noConfusion h

/-- An otherwise alternating free input with one `111` run delayed by 4j
free symbols. All family members have the same eventual alternating tail. -/
def input (j t : Nat) : Bool := if t=8*j+5 then true else pure t

theorem input_self_shift (j : Nat) : (fun t => input j (t+8*j))=base := by
  funext t
  have hm : (t+8*j)%4=t%4 := by omega
  have he : t+8*j=8*j+5 ↔ t=5 := by omega
  simp [input,base_formula,pure,hm,he]

theorem input_earlier_shift (j k : Nat) (hjk : j<k) :
    (fun t => input j (t+8*k))=pure := by
  funext t
  have he : t+8*k≠8*j+5 := by omega
  have hm : (t+8*k)%4=t%4 := by omega
  simp [input,he,pure,hm]

theorem pairwise_tail_distinct (j k : Nat) (hjk : j<k) :
    ¬TailEq (fun d => recon (input j) d 0) (fun d => recon (input k) d 0) := by
  intro h
  have ht := tail_recon_time h (8*k)
  have he (a : Nat → Bool) : (fun d => recon a d (8*k))=
      (fun d => recon (fun s => a (s+8*k)) d 0) := by
    funext d
    simpa only [Nat.zero_add] using recon_shift a (8*k) d 0
  rw [he,he,input_self_shift,input_earlier_shift j k hjk] at ht
  exact pure_not_tail_base ht

/-- No fixed spatial period, however large, covers every delayed-defect
reconstruction even after allowing a different transient for every input. -/
theorem no_common_spatial_period (P : Nat) (hP : 0<P) :
    ¬∀ j, SpatialPeriod P (fun d => recon (input j) d 0) :=
  no_common_period_of_distinct _ pairwise_tail_distinct P hP

end Rule30DelayedDefectResearch
