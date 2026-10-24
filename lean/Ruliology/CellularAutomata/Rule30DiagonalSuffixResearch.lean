module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# Reconstruction anti-diagonals and the suffix forced by finite support

These lemmas justify the scalar model used in the potential searches. They
establish no decreasing potential and do not prove a prize problem.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30DiagonalSuffixResearch

open Rule30ZeroBoundary

def diagonal (b : Nat → Bool) (n i : Nat) : Bool :=
  if i<n then recon b (i+1) (n-1-i) else false

theorem diagonal_head (b : Nat → Bool) (n : Nat) : diagonal b (n+1) 0=b n := by
  simp [diagonal,recon]

/-- Each diagonal is the prefix-xor scan of the preceding two diagonals. -/
theorem diagonal_step (b : Nat → Bool) (n i : Nat) (hi : i<n) :
    diagonal b (n+1) (i+1)=xor (diagonal b (n+1) i)
      (diagonal b n i || if i=0 then false else diagonal b (n-1) (i-1)) := by
  cases i with
  | zero =>
      simp only [diagonal,show 1<n+1 by omega,show 0<n+1 by omega,show 0<n by omega,
        ite_true]
      rw [show n+1-1-1=n-1 by omega,show n+1-1-0=n by omega,
        show n-1-0=n-1 by omega]
      rw [recon_two]
      simp [recon,show n-1+1=n by omega]
  | succ i =>
      simp only [diagonal,show i+1+1<n+1 by omega,show i+1<n+1 by omega,
        show i+1<n by omega,ite_true,
        show i+1≠0 by omega,ite_false]
      rw [show i+1-1=i by omega,show n+1-1-(i+1+1)=n-1-(i+1) by omega,
        show n+1-1-(i+1)=(n-1-(i+1))+1 by omega,
        show n-1-1-i=n-1-(i+1) by omega]
      simp only [show i<n-1 by omega,ite_true]
      exact recon_two b (i+1) (n-1-(i+1))

theorem diagonal_lower (b : Nat → Bool) (n i : Nat) (hi : i+1<n) :
    (diagonal b (n-1) i && !(xor (diagonal b n i) (diagonal b n (i+1))))=false := by
  have hs := diagonal_step b (n-1) i (by omega)
  rw [show n-1+1=n by omega] at hs
  rw [hs]
  cases diagonal b n i <;> cases diagonal b (n-1) i <;>
    cases (if i=0 then false else diagonal b (n-1-1) (i-1)) <;> rfl

/-- The stronger upper ribbon constraint also holds on actual reconstruction diagonals. -/
theorem diagonal_upper (b : Nat → Bool) (n i : Nat) (hi : i+1<n) :
    (xor (diagonal b n i) (diagonal b n (i+1)) &&
      !(diagonal b (n-1) i || if i=0 then false else diagonal b (n-1) (i-1)))=false := by
  have hs := diagonal_step b (n-1) i (by omega)
  rw [show n-1+1=n by omega] at hs
  rw [hs]
  cases i with
  | zero =>
      simp only [ite_true] at *
      cases diagonal b n 0 <;> cases diagonal b (n-1) 0 <;> rfl
  | succ i =>
      simp only [show i+1≠0 by omega,ite_false,show i+1-1=i by omega]
      have hl := diagonal_lower b (n-1) i (by omega)
      rw [show n-1-1=n-2 by omega] at hl ⊢
      cases ha : diagonal b n (i+1) <;>
      cases hb : diagonal b (n-1) (i+1) <;>
      cases hc : diagonal b (n-1) i <;>
      cases hd : diagonal b (n-2) i <;> simp_all

theorem diagonal_false_of_finite (b : Nat → Bool) (W : Nat)
    (hW : ∀ k, W<k → lam b k=false) (n i : Nat) (hi : i<n)
    (hfar : W+n<2*i+2) : diagonal b n i=false := by
  rw [diagonal,ite_eq_left hi,← zrow_lam]
  exact zrow_fin hW (n-1-i) (i+1) (by omega)

/-- Every fixed suffix width is eventually white, uniformly over its positions. -/
theorem eventual_white_suffix (b : Nat → Bool) (W s : Nat)
    (hW : ∀ k, W<k → lam b k=false) (n : Nat) (hn : W+2*s<n) :
    ∀ i, n-s≤i → i<n → diagonal b n i=false := by
  intro i his hin
  exact diagonal_false_of_finite b W hW n i hin (by omega)

end Ruliology.CellularAutomata.Rule30DiagonalSuffixResearch
