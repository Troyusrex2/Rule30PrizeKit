import PhysicalEarlyCases
import PhysicalCapture

/-! A symbolic stripe invariant with linear white padding, conditional on entry. -/
namespace PhysicalMaintenance
open Ruliology.CellularAutomata Rule30Jen

def horizon (N : Nat) : Nat := 2*N+1
def padding (N : Nat) : Nat := (N+1)+9*horizon N
def StripeAt (N t : Nat) : Prop :=
  ∀ p : Int, 1 ≤ p → p ≤ 2*(horizon N:Int)+1 →
    cell t p = PhysicalEarlyCases.stripe p

/-- The finite block followed by q white driver ticks. Nothing is assumed afterwards. -/
def Drives (t : Nat) (u : List Bool) (q : Nat) : Prop :=
  ∀ s, s < u.length+q → cell (t+s) 0 = u.getD s false

theorem padding_eq (N : Nat) : padding N = 19*N+10 := by
  unfold padding horizon
  omega

theorem exists_last (u : List Bool) : ∀ m, m ≤ u.length →
    (∃ j, j < m ∧ u.getD j false = true) →
    ∃ j, j < m ∧ u.getD j false = true ∧
      ∀ j', j < j' → j' < m → u.getD j' false = false
  | 0, _, ⟨j,hj,_⟩ => by omega
  | m+1, hm, ⟨j,hj,hb⟩ => by
    cases hc : u.getD m false with
    | true => exact ⟨m,by omega,hc,fun j' h1 h2 => by omega⟩
    | false =>
      have hjm : j < m := by
        by_cases he : j=m
        · subst j; rw [hc] at hb; cases hb
        · omega
      obtain ⟨j0,h1,h2,h3⟩ := exists_last u m (by omega) ⟨j,hjm,hb⟩
      refine ⟨j0,by omega,h2,fun j' hj1 hj2 => ?_⟩
      by_cases hlt : j' < m
      · exact h3 j' hj1 hlt
      · have he : j'=m := by omega
        subst j'; exact hc

/-- The even middle cell of the incoming stripe survives any fewer than N ticks. -/
theorem short_white_witness (N t ell : Nat) (hN : 1 ≤ N) (hell : ell < N)
    (hstripe : StripeAt N t) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ N+1 ∧ cell (t+ell) p = false := by
  let p := N+N%2
  have hp1 : 1 ≤ p := by dsimp [p]; omega
  have hpB : p ≤ N+1 := by dsimp [p]; omega
  have hpl : (1:Int)+ell ≤ (p:Int) := by dsimp [p]; omega
  have hpu : (p:Int)+ell ≤ 2*(horizon N:Int)+1 := by
    dsimp [p,horizon]
    omega
  have hh := PhysicalEarlyCases.stationary_cone PhysicalEarlyCases.stripe
    PhysicalEarlyCases.stripe_stationary t 1 (2*(horizon N:Int)+1)
    hstripe ell p hpl hpu
  have heven : (p:Int)%2=0 := by dsimp [p]; omega
  refine ⟨p,hp1,hpB,?_⟩
  simpa [PhysicalEarlyCases.stripe,heven] using hh

/-- A black-containing block of length at most N preserves the stripe after linear padding. -/
theorem maintain (N t : Nat) (u : List Bool) (q : Nat)
    (hN : 1 ≤ N) (hlen : u.length ≤ N)
    (hblack : ∃ ell, ell < u.length ∧ u.getD ell false = true)
    (hq : padding N ≤ q) (hstripe : StripeAt N t) (hdrive : Drives t u q) :
    (∀ s, horizon N ≤ s → s ≤ u.length+q → cell (t+s) 1 = true) ∧
    StripeAt N (t+u.length+q) := by
  obtain ⟨ell,hell,hbell,hlast⟩ := exists_last u u.length (Nat.le_refl _) hblack
  have hwitness := short_white_witness N t ell hN (by omega) hstripe
  have h0 : cell (t+ell) 0 = true := by
    rw [hdrive ell (by omega)]
    exact hbell
  let L := u.length+q-ell-1
  have hL : (N+1)+9*horizon N ≤ L := by
    change (N+1)+9*horizon N ≤ q at hq
    dsimp [L]
    omega
  have hw : ∀ s, s < L → cell (t+ell+1+s) 0 = false := by
    intro s hs
    have hsp : ell+1+s < u.length+q := by dsimp [L] at hs; omega
    rw [show t+ell+1+s=t+(ell+1+s) by omega,hdrive (ell+1+s) hsp]
    by_cases hu : ell+1+s < u.length
    · exact hlast (ell+1+s) (by omega) hu
    · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)]
      rfl
  obtain ⟨htail,hregen⟩ := PhysicalCapture.tail_and_stripe
    (t+ell) (N+1) (horizon N) L h0 hwitness hw hL
  constructor
  · intro s hs hsP
    have hB : N+1 ≤ s-ell-1 := by dsimp [horizon] at hs; omega
    have hsL : s-ell-1 ≤ L := by dsimp [L]; omega
    have hh := htail (s-ell-1) hB hsL
    have he : t+ell+1+(s-ell-1)=t+s := by dsimp [horizon] at hs; omega
    simpa only [he] using hh
  · intro p hp1 hpK
    have he : t+ell+1+L=t+u.length+q := by dsimp [L]; omega
    simpa only [he] using hregen p hp1 hpK

/-- Boundary agreement is needed only before the time horizon, not for the entire future. -/
theorem finite_cone_agree (t0 t1 M H : Nat)
    (hdrv : ∀ r, r < H → cell (t0+r) 0 = cell (t1+r) 0)
    (hrow : ∀ p : Int, 1 ≤ p → p ≤ M → cell t0 p = cell t1 p) :
    ∀ s : Nat, s ≤ H → ∀ p : Int, 1 ≤ p → p+s ≤ M →
      cell (t0+s) p = cell (t1+s) p
  | 0, _, p, h1, h2 => by simpa using hrow p h1 (by omega)
  | s+1, hs, p, h1, h2 => by
    show rule (cell (t0+s) (p-1)) (cell (t0+s) p) (cell (t0+s) (p+1)) =
      rule (cell (t1+s) (p-1)) (cell (t1+s) p) (cell (t1+s) (p+1))
    have hl : cell (t0+s) (p-1) = cell (t1+s) (p-1) := by
      by_cases hp : p=1
      · rw [show p-1=0 by omega]
        exact hdrv s (by omega)
      · exact finite_cone_agree t0 t1 M H hdrv hrow s (by omega)
          (p-1) (by omega) (by omega)
    rw [hl,finite_cone_agree t0 t1 M H hdrv hrow s (by omega) p h1 (by omega),
      finite_cone_agree t0 t1 M H hdrv hrow s (by omega) (p+1) (by omega) (by omega)]

/-- The complete response to the same block agrees, even with different admissible padding.
The equality includes the shorter segment's endpoint. Future blocks are unrestricted. -/
theorem response_agree (N t0 t1 : Nat) (u : List Bool) (q0 q1 : Nat)
    (hN : 1 ≤ N) (hlen : u.length ≤ N)
    (hblack : ∃ ell, ell < u.length ∧ u.getD ell false = true)
    (hq0 : padding N ≤ q0) (hq1 : padding N ≤ q1)
    (hs0 : StripeAt N t0) (hs1 : StripeAt N t1)
    (hd0 : Drives t0 u q0) (hd1 : Drives t1 u q1) :
    ∀ s, s ≤ u.length+q0 → s ≤ u.length+q1 →
      cell (t0+s) 1 = cell (t1+s) 1 := by
  have hb0 := (maintain N t0 u q0 hN hlen hblack hq0 hs0 hd0).1
  have hb1 := (maintain N t1 u q1 hN hlen hblack hq1 hs1 hd1).1
  intro s hsP0 hsP1
  by_cases hsK : s < horizon N
  · have hdrv : ∀ r, r < s → cell (t0+r) 0 = cell (t1+r) 0 := by
      intro r hr
      rw [hd0 r (by omega),hd1 r (by omega)]
    have hrow : ∀ p : Int, 1 ≤ p → p ≤ (2*horizon N+1:Nat) →
        cell t0 p = cell t1 p := by
      intro p hp1 hpK
      rw [hs0 p hp1 (by omega),hs1 p hp1 (by omega)]
    exact finite_cone_agree t0 t1 (2*horizon N+1) s hdrv hrow s (by omega)
      1 (by omega) (by omega)
  · rw [hb0 s (by omega) hsP0,hb1 s (by omega) hsP1]

end PhysicalMaintenance
