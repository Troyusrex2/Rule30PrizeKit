module
public import RankEscape
public import TwoClockAlias
@[expose] public section
namespace ControlledBudget
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration RelativeRank RankEscape
open TwoClockAlias (U)

def budget (c h : Bool) (x y : Code) : Nat :=
  rank (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    (xor (x 1) (y 1)) (xor (x 2) (y 2)) (xor (x 3) (y 3)) c h

theorem budget_step (c h cp hp : Bool) (x y : Code)
    (compatible : h=true → cp≠c) (different : x 0≠y 0)
    (a : x 4=y 4) (b : x 5=y 5)
    (a1 : U c h x 4=U c h y 4) (b1 : U c h x 5=U c h y 5) :
    budget cp hp (U c h x) (U c h y)+(if c then 1 else 0)≤budget c h x y := by
  have neg:=neq_neg _ _ different
  have e4 : xor (x 4) (x 3||x 2)=xor (x 4) (y 3||y 2) := by
    simpa only [U,←a] using a1
  have e5 : xor (x 5) (x 4||x 3)=xor (x 5) (x 4||y 3) := by
    simpa only [U,←a,←b] using b1
  have cert:=rank_certificate (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    (xor (x 1) (y 1)) (xor (x 2) (y 2)) (xor (x 3) (y 3)) c h cp hp compatible
    (by simpa only [unxor] using e4) (by simpa only [unxor] using e5)
  simpa only [budget,U,unxor,neg] using cert

theorem recurrent_rank_impossible (r : Nat → Nat) (c : Nat → Bool)
    (step : ∀ t,r (t+1)+(if c t then 1 else 0)≤r t)
    (recurrent : ∀ s,∃ t,s≤t ∧ c t=true) : False := by
  have main : ∀ m,∀ (a : Nat → Nat) (b : Nat → Bool),
      a 0≤m → (∀ u,a (u+1)+(if b u then 1 else 0)≤a u) →
      (∀ s,∃ t,s≤t ∧ b t=true) → False := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro a b bound steps recur
      obtain ⟨t,ht,black⟩:=recur 0
      have weak : ∀ u,u<t+1 → a (u+1)≤a u := by
        intro u hu;have h:=steps u;omega
      have before:=rank_chain a (t+1) weak t 0 (by omega)
      simp only [Nat.zero_add] at before
      have strict:=steps t
      rw [black] at strict
      change a (t+1)+1≤a t at strict
      apply ih (a (t+1)) (by omega) (fun u => a (t+1+u)) (fun u => b (t+1+u)) (Nat.le_refl _)
      · intro u
        simpa only [Nat.add_assoc] using steps (t+1+u)
      · intro s
        obtain ⟨w,hw,hb⟩:=recur (t+1+s)
        refine ⟨w-(t+1),by omega,?_⟩
        have idx : t+1+(w-(t+1))=w := by omega
        simpa only [idx] using hb
  exact main (r 0) r c (Nat.le_refl _) step recurrent

/-- Uniform over arbitrary infinite control streams. Four-digit trapping
is impossible when the lower clock is recurrently black and its immediate
ancestor compatibility is respected. No quantitative recurrence is needed. -/
theorem no_four_digit_trap (X Y : Nat → Code) (c h : Nat → Bool)
    (xstep : ∀ t,X (t+1)=U (c t) (h t) (X t))
    (ystep : ∀ t,Y (t+1)=U (c t) (h t) (Y t))
    (compatible : ∀ t,h t=true → c (t+1)≠c t)
    (different : X 0 0≠Y 0 0)
    (recurrent : ∀ s,∃ t,s≤t ∧ c t=true)
    (confined : ∀ t, X t 4=Y t 4 ∧ X t 5=Y t 5) : False := by
  have diff : ∀ t,X t 0≠Y t 0 := by
    intro t
    induction t with
    | zero => exact different
    | succ t ih =>
      rw [xstep,ystep]
      change xor (X t 0) (c t||h t)≠xor (Y t 0) (c t||h t)
      cases a:X t 0 <;> cases b:Y t 0 <;> cases d:(c t||h t) <;> simp_all
  apply recurrent_rank_impossible (fun t => budget (c t) (h t) (X t) (Y t)) c ?_ recurrent
  intro t
  rw [xstep,ystep]
  exact budget_step (c t) (h t) (c (t+1)) (h (t+1)) (X t) (Y t) (compatible t) (diff t)
    (confined t).1 (confined t).2
    (by rw [←xstep,←ystep];exact (confined (t+1)).1)
    (by rw [←xstep,←ystep];exact (confined (t+1)).2)

/-- The five-digit counterexample satisfies TWO full lower recurrences,
has recurrent black input and remains nontrivial forever. This is the
sharp width threshold for the relaxed controlled model, not a pair with
genuine finite black-edge ancestors. -/
theorem five_digit_recurrent_trap :
    let X:=fun t => TwoClockAlias.driven t (TwoClockAlias.code 106)
    let Y:=fun t => TwoClockAlias.driven t (TwoClockAlias.code 113)
    let c:=fun t => TwoClockAlias.clockC (TwoClockAlias.phase t)
    let h:=fun t => TwoClockAlias.clockH (TwoClockAlias.phase t)
    let g:=fun t => TwoClockAlias.clockG (TwoClockAlias.phase t)
    let f:=fun t => TwoClockAlias.clockF (TwoClockAlias.phase t)
    (∀ t,X (t+1)=U (c t) (h t) (X t)) ∧
    (∀ t,Y (t+1)=U (c t) (h t) (Y t)) ∧
    (∀ t,c (t+1)=xor (c t) (h t||g t)) ∧
    (∀ t,h (t+1)=xor (h t) (g t||f t)) ∧
    (∀ s,∃ t,s≤t ∧ c t=true) ∧
    (∀ t,X t 0≠Y t 0) ∧
    (∀ t j,5≤j → X t j=Y t j) := by
  refine ⟨?_,?_,?_,?_,?_,TwoClockAlias.different_forever,TwoClockAlias.controlled_confined⟩
  · intro t;exact TwoClockAlias.actual_control_step _ _
  · intro t;exact TwoClockAlias.actual_control_step _ _
  · intro t;exact (TwoClockAlias.two_ancestor_recurrences _).1
  · intro t;exact (TwoClockAlias.two_ancestor_recurrences _).2
  · intro s
    exact ⟨16*(s+1),by omega,TwoClockAlias.actual_recurrent_black (s+1)⟩

theorem no_black_tick_budget_for_five_digit_example (r : Nat → Nat)
    (step : ∀ t,r (t+1)+(if TwoClockAlias.clockC (TwoClockAlias.phase t) then 1 else 0)≤r t) : False := by
  apply recurrent_rank_impossible r _ step
  intro s
  exact ⟨16*(s+1),by omega,TwoClockAlias.actual_recurrent_black (s+1)⟩

end ControlledBudget
