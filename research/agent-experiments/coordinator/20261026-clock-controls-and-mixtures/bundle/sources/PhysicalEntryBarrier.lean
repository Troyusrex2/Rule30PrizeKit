import PhysicalMaintenance

/-! Necessary conditions for failure of stripe entry. No automatic-entry theorem is asserted. -/
namespace PhysicalEntryBarrier
open Ruliology.CellularAutomata Rule30Jen Rule30BlackRuns PhysicalMaintenance

def NarrowStripe (N t : Nat) : Prop :=
  ∀ p : Int, 1 ≤ p → p ≤ 2*(N:Int)+1 →
    cell t p = PhysicalEarlyCases.stripe p

theorem narrow_white_witness (N t ell : Nat) (hN : 1 ≤ N) (hell : ell < N)
    (hstripe : NarrowStripe N t) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ N+1 ∧ cell (t+ell) p = false := by
  let p := N+N%2
  have hp1 : 1 ≤ p := by dsimp [p]; omega
  have hpB : p ≤ N+1 := by dsimp [p]; omega
  have hpl : (1:Int)+ell ≤ (p:Int) := by dsimp [p]; omega
  have hpu : (p:Int)+ell ≤ 2*(N:Int)+1 := by dsimp [p]; omega
  have hh := PhysicalEarlyCases.stationary_cone PhysicalEarlyCases.stripe
    PhysicalEarlyCases.stripe_stationary t 1 (2*(N:Int)+1) hstripe ell p hpl hpu
  have heven : (p:Int)%2=0 := by dsimp [p]; omega
  refine ⟨p,hp1,hpB,?_⟩
  simpa [PhysicalEarlyCases.stripe,heven] using hh

/-- A narrow incoming stripe regenerates the frozen BIG stripe under the OLD padding bound. -/
theorem narrow_to_big (N t : Nat) (u : List Bool) (q : Nat)
    (hN : 1 ≤ N) (hlen : u.length ≤ N)
    (hblack : ∃ ell, ell < u.length ∧ u.getD ell false = true)
    (hq : padding N ≤ q) (hstripe : NarrowStripe N t) (hdrive : Drives t u q) :
    StripeAt N (t+u.length+q) := by
  obtain ⟨ell,hell,hbell,hlast⟩ := PhysicalMaintenance.exists_last u u.length
    (Nat.le_refl _) hblack
  have hwitness := narrow_white_witness N t ell hN (by omega) hstripe
  have h0 : cell (t+ell) 0 = true := by rw [hdrive ell (by omega)]; exact hbell
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
  have hregen := (PhysicalCapture.tail_and_stripe
    (t+ell) (N+1) (horizon N) L h0 hwitness hw hL).2
  intro p hp1 hpK
  have he : t+ell+1+L=t+u.length+q := by dsimp [L]; omega
  simpa only [he] using hregen p hp1 hpK

/-- Failed narrow entry forces a black prefix at the preceding black tick. -/
theorem failed_narrow_black_prefix (t N L : Nat) (h0 : cell t 0 = true)
    (hw : ∀ s, s < L → cell (t+1+s) 0 = false) (hL : 9*N ≤ L)
    (hfail : ¬ NarrowStripe N (t+1+L)) :
    ∀ p : Nat, 1 ≤ p → p ≤ L-9*N → cell t p = true := by
  intro p hp1 hpB
  cases hc : cell t p with
  | true => rfl
  | false =>
    have hregen := (PhysicalCapture.tail_and_stripe t (L-9*N) N L h0
      ⟨p,hp1,hpB,hc⟩ hw (by omega)).2
    exact (hfail hregen).elim

/-- Failed narrow entry requires a white column1 at the final shield deadline.
The endpoint itself is not claimed white; late arrival remains possible. -/
theorem failed_narrow_deadline_white (t N L : Nat)
    (hw : ∀ s, s < L → cell (t+1+s) 0 = false) (hL : 9*N ≤ L)
    (hfail : ¬ NarrowStripe N (t+1+L)) :
    cell (t+1+(L-9*N)) 1 = false := by
  cases hc : cell (t+1+(L-9*N)) 1 with
  | false => rfl
  | true =>
    have hb := black_stays (t+1+(L-9*N)) (9*N) (fun s hs => by
      have hh := hw (L-9*N+s) (by omega)
      simpa only [show t+1+(L-9*N+s)=t+1+(L-9*N)+s by omega] using hh) hc
    have hregen := PhysicalCapture.stripe_after_black_run (t+1+(L-9*N)) N
      (fun s hs => hb s (by omega)) (hb (9*N) (Nat.le_refl _))
    have he : t+1+(L-9*N)+9*N=t+1+L := by omega
    rw [he] at hregen
    exact (hfail hregen).elim

end PhysicalEntryBarrier
