import Rule30RoundTwoChargeTwoEntryResearch

namespace Rule30RoundTwoChargeTwoThetaResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundary
open Rule30RoundTwoChargeTwoEntryResearch (right stream)

def columns : List (List Bool) :=
[
  [false, false, false, false, false, false, false, false],
  [true, false, true, true, true, true, true, false],
  [true, true, false, false, false, false, true, true],
  [false, true, true, true, true, false, false, true],
  [false, false, false, false, true, false, false, false],
  [false, true, true, false, true, false, false, false],
  [true, false, true, true, true, false, false, true],
  [true, false, false, false, true, false, true, false],
  [true, false, true, false, true, true, true, false],
  [true, true, true, true, false, false, true, true],
  [false, false, false, true, true, false, false, true],
  [true, true, false, false, true, false, false, false],
  [false, true, false, false, true, false, false, false],
  [false, true, false, true, true, false, false, true],
  [true, true, true, false, true, false, true, false],
  [false, false, true, false, true, true, true, false],
  [true, false, true, true, false, false, true, true],
  [true, true, false, true, true, false, false, true],
  [false, true, false, false, true, false, false, false],
  [false, true, false, false, true, false, false, false],
  [true, true, false, true, true, false, false, true],
  [false, true, true, false, true, false, true, false],
  [false, false, true, false, true, true, true, false],
  [false, false, true, true, false, false, true, true],
  [false, true, false, true, true, false, false, true],
  [true, true, false, false, true, false, false, false]
]

def timeAt (t : Nat) : Nat := if t<4 then t else 4+(t-4)%4
def timeNext (t : Nat) : Nat := if t=7 then 4 else t+1
def spaceAt (d : Nat) : Nat := if d<12 then d else 12+(d-12)%14
def spaceNext (d : Nat) : Nat := if d=25 then 12 else d+1
def raw (d t : Nat) : Bool := (columns.getD d []).getD t false
def model (d t : Nat) : Bool := raw (spaceAt d) (timeAt t)
def left (d : Nat) : Bool := model d 0

theorem timeAt_lt (t : Nat) : timeAt t<8 := by unfold timeAt; split <;> omega
theorem spaceAt_lt (d : Nat) : spaceAt d<26 := by unfold spaceAt; split <;> omega

theorem timeAt_succ (t : Nat) : timeAt (t+1)=timeNext (timeAt t) := by
  unfold timeAt timeNext
  split <;> split <;> split <;> omega

theorem spaceAt_succ (d : Nat) : spaceAt (d+1)=spaceNext (spaceAt d) := by
  unfold spaceAt spaceNext
  split <;> split <;> split <;> omega

theorem table_rule : ∀ d, d<26 → ∀ t, t<8 →
    raw (spaceNext (spaceNext d)) t =
      xor (raw (spaceNext d) (timeNext t)) (raw (spaceNext d) t || raw d t) := by
  have checked : (List.range 26).all (fun d => (List.range 8).all fun t =>
    raw (spaceNext (spaceNext d)) t ==
      xor (raw (spaceNext d) (timeNext t)) (raw (spaceNext d) t || raw d t)) = true := by decide +kernel
  intro d hd t ht
  exact beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp checked d (List.mem_range.mpr hd)) t (List.mem_range.mpr ht))

theorem model_rule (d t : Nat) : model (d+2) t =
    xor (model (d+1) (t+1)) (model (d+1) t || model d t) := by
  unfold model
  rw [show d+2=(d+1)+1 by omega,spaceAt_succ,spaceAt_succ,timeAt_succ]
  exact table_rule _ (spaceAt_lt d) _ (timeAt_lt t)

theorem model_zero (t : Nat) : model 0 t=false := by
  have checked : (List.range 8).all (fun t => raw 0 t == false) = true := by decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp checked (timeAt t) (List.mem_range.mpr (timeAt_lt t)))

theorem model_one (t : Nat) : model 1 t=alt stream t := by
  by_cases ht : t<4
  · have hs : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hs with hs|hs|hs|hs <;> subst t <;> decide +kernel
  · have hp : t%4=0 ∨ t%4=1 ∨ t%4=2 ∨ t%4=3 := by omega
    rcases hp with hp|hp|hp|hp
    all_goals
      have hi : (t-4)%4=t%4 := by omega
      have hsmall : ¬t/2<2 := by omega
      have h2 : t%2=(t%4)%2 := by omega
      have hh : (t/2)%2=(t%4)/2 := by omega
      simp [model,raw,columns,spaceAt,timeAt,alt,stream,ht,hi,hsmall,h2,hh,hp]

theorem recon_model_pair (d : Nat) :
    (∀ t, recon (alt stream) d t=model d t) ∧
    (∀ t, recon (alt stream) (d+1) t=model (d+1) t) := by
  induction d with
  | zero => exact ⟨fun t => (model_zero t).symm,fun t => (model_one t).symm⟩
  | succ d ih =>
    refine ⟨ih.2,fun t => ?_⟩
    rw [recon,ih.2 (t+1),ih.2 t,ih.1 t]
    exact (model_rule d t).symm

theorem theta_left : Theta stream=left := by
  funext d
  exact (recon_model_pair d).1 0

theorem psi_left : Rule30PeriodTwoSideways.Psi right=left := by
  have hf : (fun s => !Rule30PeriodTwoSideways.u right s)=stream := by
    funext s
    simpa only [Rule30CriticalChargeOneCoreResearch.free,Rule30PeriodTwoSideways.Psi_free,
      Rule30PeriodTwoSideways.u] using Rule30RoundTwoChargeTwoEntryResearch.free_stream s
  unfold Rule30PeriodTwoSideways.Psi
  rw [hf,theta_left]

end Rule30RoundTwoChargeTwoThetaResearch
