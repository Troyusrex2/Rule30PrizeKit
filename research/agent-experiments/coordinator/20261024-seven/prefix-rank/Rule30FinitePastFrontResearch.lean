import Rule30VacuumPrefixRankObstructionResearch

/-! A finite-past restriction genuinely excludes the first row of the
forward-only rank obstruction. The two-step moving front always has
suffix false,true,true, independently of the finite initial row. -/

namespace Rule30FinitePastFrontResearch
open Ruliology.CellularAutomata.Rule30ZeroBoundary
open Rule30FiniteLeftWordResearch (row row_support)
open Rule30VacuumPrefixRankObstructionResearch (w0 w0_length)

theorem one_step_inside_front {L : Nat → Bool} {m : Nat} (hm : 1≤m)
    (he : L m=true) (hf : ∀ k,m<k → L k=false) :
    zrow L 1 m=true := by
  obtain ⟨k,hk⟩ : ∃ k,m=k+1 := ⟨m-1,by omega⟩
  subst m
  rw [zrow_succ,zrow_zero,zrow_zero,he]
  rw [hf (k+2) (by omega)]
  rfl

theorem two_step_front {L : Nat → Bool} {m : Nat} (hm : 1≤m)
    (he : L m=true) (hf : ∀ k,m<k → L k=false) :
    zrow L 2 m=false ∧ zrow L 2 (m+1)=true ∧ zrow L 2 (m+2)=true := by
  have h1:=zrow_edge hm he hf 1
  have h2:=zrow_edge hm he hf 2
  have hi:=one_step_inside_front hm he hf
  refine ⟨?_,?_,h2.1⟩
  · obtain ⟨k,hk⟩ : ∃ k,m=k+1 := ⟨m-1,by omega⟩
    subst m
    rw [show 2=1+1 by omega,zrow_succ,h1.1,hi]
    cases zrow L 1 k <;> rfl
  · rw [show 2=1+1 by omega,zrow_succ,h1.2 (m+2) (by omega),h1.1,hi]
    rfl

theorem obstruction_last_black : row w0 30=true := by decide +kernel

theorem obstruction_not_finite_image {L : Nat → Bool} (hL : FinSupp L)
    (hhead : L 1=true) : zrow L 2≠row w0 := by
  intro heq
  obtain ⟨W,hW⟩:=hL
  obtain ⟨m,hm,he,hf⟩:=last_black hhead W hW
  have hedge:=zrow_edge hm he hf 2
  have h30 : zrow L 2 30=true := by rw [heq];exact obstruction_last_black
  have hlen : m+2=30 := by
    have hle : m+2≤30 := by
      apply Classical.byContradiction
      intro hn
      have hz:=row_support w0 (m+2) (by rw [w0_length];omega)
      rw [←heq,hedge.1] at hz
      cases hz
    have hge : 30≤m+2 := by
      apply Classical.byContradiction
      intro hn
      have hz:=hedge.2 30 (by omega)
      rw [h30] at hz
      cases hz
    omega
  have hm28 : m=28 := by omega
  have hz:=(two_step_front hm he hf).1
  rw [heq,hm28] at hz
  have ht : row w0 28=true := by decide +kernel
  rw [ht] at hz
  cases hz

end Rule30FinitePastFrontResearch
