import CedarPhysicalAgeBridge
import PhysicalCapture
import Ruliology.CellularAutomata.Rule30StripCertificates

/-! Arbitrary blocks with sufficiently long white padding, by symbolic stripe regeneration. -/
namespace CedarPaddingExclusion
open Ruliology.CellularAutomata Rule30Jen Rule30BlackRuns
open Rule30StripCertificates CedarPhysicalAgeBridge

def stripeWidth (n : Nat) : Nat := n + bound n
def paddingThreshold (n : Nat) : Nat :=
  max (warmup n) (bound n + 9*stripeWidth n)

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

/-- Phasewise agreement from period number two gives the exact eventual onset T+2P. -/
theorem phase_periodic (f : Nat → Bool) (T P : Nat) (hP : 0 < P)
    (hphase : ∀ m, 2 ≤ m → ∀ s, s < P →
      f (T+(m+1)*P+s) = f (T+m*P+s)) :
    ∀ t, T+2*P ≤ t → f (t+P) = f t := by
  intro t ht
  let k := (t-(T+2*P))/P
  let s := (t-(T+2*P))%P
  have hs : s < P := Nat.mod_lt _ hP
  have hd : s+P*k=t-(T+2*P) := Nat.mod_add_div _ _
  have htime : t=T+(k+2)*P+s := by
    rw [Nat.add_mul]
    rw [Nat.mul_comm P k] at hd
    omega
  have hnext : t+P=T+((k+2)+1)*P+s := by
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega
  rw [hnext,htime]
  exact hphase (k+2) (Nat.le_add_left 2 k) s hs

/-- An arbitrary black-containing block is excluded with the explicit white padding bound. -/
theorem not_eventually_padded_word (u : List Bool) (q : Nat)
    (hblack : ∃ j, j < u.length ∧ u.getD j false = true)
    (hq : paddingThreshold u.length ≤ q) :
    ¬ EventuallyWord (u ++ List.replicate q false) := by
  intro hevent
  obtain ⟨T,hT⟩ := hevent
  let n := u.length
  let B := bound n
  let W := warmup n
  let K := n+B
  let P := n+q
  let w := u ++ List.replicate q false
  have hn : 1 ≤ n := by obtain ⟨j,hj,_⟩ := hblack; dsimp [n]; omega
  have hW : W ≤ q := Nat.le_trans (Nat.le_max_left _ _) hq
  have hqB : B+9*K ≤ q := Nat.le_trans (Nat.le_max_right _ _) hq
  have hP : 0 < P := by dsimp [P]; omega
  have hwlen : w.length=P := by simp [w,P,n]
  change ∀ t, T ≤ t → cell t 0 = w.getD ((t-T)%w.length) false at hT
  rw [hwlen] at hT
  have hper : ∀ t, T ≤ t → cell (t+P) 0 = cell t 0 := by
    intro t ht
    rw [hT (t+P) (by omega),hT t ht,
      show t+P-T=(t-T)+P by omega,Nat.add_mod_right]
  have hblock : ∀ m s, s < P → cell (T+m*P+s) 0 = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega),show T+m*P+s-T=s+m*P by omega,
      Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hs]
  have hgetu : ∀ j, j < n → w.getD j false = u.getD j false := by
    intro j hj
    simp only [w,List.getD_eq_getElem?_getD,List.getElem?_append_left hj]
  have hgetw : ∀ j, n ≤ j → j < P → w.getD j false = false := by
    intro j hj1 hj2
    rw [show w=u++List.replicate q false by rfl,List.getD_eq_getElem?_getD,
      List.getElem?_append_right hj1,List.getElem?_replicate,
      ite_eq_left (by dsimp [P,n] at *; omega)]
    rfl
  obtain ⟨ell,hell,hbell,hlast⟩ := exists_last u n (Nat.le_refl _) hblack
  have htailwhite : ∀ m s, ell < s → s < P → cell (T+m*P+s) 0 = false := by
    intro m s hs hsp
    rw [hblock m s hsp]
    by_cases hsn : s < n
    · rw [hgetu s hsn]
      exact hlast s hs hsn
    · exact hgetw s (by omega) hsp
  have hnext : ∀ m, T+(m+1)*P=T+m*P+P := by
    intro m
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega
  have hcapture : ∀ m, 1 ≤ m →
      (∀ s, K ≤ s → s ≤ P → cell (T+m*P+s) 1 = true) ∧
      (∀ p : Int, 1 ≤ p → p ≤ 2*(K:Int)+1 →
        cell (T+(m+1)*P) p = PhysicalEarlyCases.stripe p) := by
    intro m hm
    have hprev : (m-1)*P+P=m*P := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    let t0 := T+(m-1)*P+(P-W)
    have hWP : W ≤ P := by dsimp [P]; omega
    have ht0 : t0+W=T+m*P := by dsimp [t0]; omega
    have hwhite : ∀ r, r < warmup n → cell (t0+r) 0 = false := by
      intro r hr
      have hphase : n ≤ P-W+r := by dsimp [P,W] at *; omega
      have hphaseP : P-W+r < P := by change r < W at hr; omega
      rw [show t0+r=T+(m-1)*P+(P-W+r) by dsimp [t0]; omega,
        hblock (m-1) (P-W+r) hphaseP,hgetw _ hphase hphaseP]
    obtain ⟨p,hp1,hpB,hpw⟩ := physical_white_witness t0 n ell hn hell hwhite
    have hwitness : ∃ p : Nat, 1 ≤ p ∧ p ≤ B ∧ cell (T+m*P+ell) p = false := by
      refine ⟨p,hp1,hpB,?_⟩
      change cell (t0+W+ell) p = false at hpw
      simpa only [ht0] using hpw
    have hblackell : cell (T+m*P+ell) 0 = true := by
      rw [hblock m ell (by dsimp [P]; omega),hgetu ell hell]
      exact hbell
    let L := P-ell-1
    have hL : B+9*K ≤ L := by dsimp [L,P,K] at *; omega
    have hwhiteL : ∀ s, s < L → cell (T+m*P+ell+1+s) 0 = false := by
      intro s hs
      have hsp : ell+1+s < P := by dsimp [L] at hs; omega
      have hh := htailwhite m (ell+1+s) (by omega) hsp
      simpa only [show T+m*P+(ell+1+s)=T+m*P+ell+1+s by omega] using hh
    obtain ⟨htail,hstripe⟩ := PhysicalCapture.tail_and_stripe
      (T+m*P+ell) B K L hblackell hwitness hwhiteL hL
    constructor
    · intro s hs hsP
      have hBs : B ≤ s-ell-1 := by dsimp [K] at hs; omega
      have hsL : s-ell-1 ≤ L := by dsimp [L]; omega
      have hh := htail (s-ell-1) hBs hsL
      have he : T+m*P+ell+1+(s-ell-1)=T+m*P+s := by dsimp [K] at hs; omega
      simpa only [he] using hh
    · intro p hp1 hpK
      have he : T+m*P+ell+1+L=T+(m+1)*P := by
        rw [hnext]
        dsimp [L]
        dsimp [P] at *
        omega
      simpa only [he] using hstripe p hp1 hpK
  have hstripe : ∀ m, 2 ≤ m → ∀ p : Int, 1 ≤ p → p ≤ 2*(K:Int)+1 →
      cell (T+m*P) p = PhysicalEarlyCases.stripe p := by
    intro m hm p hp1 hpK
    have hh := (hcapture (m-1) (by omega)).2 p hp1 hpK
    simpa only [show m-1+1=m by omega] using hh
  have hphase : ∀ m, 2 ≤ m → ∀ s, s < P →
      cell (T+(m+1)*P+s) 1 = cell (T+m*P+s) 1 := by
    intro m hm s hs
    by_cases hsK : s < K
    · have hdriver : ∀ r, cell (T+m*P+r) 0 = cell (T+(m+1)*P+r) 0 := by
        intro r
        have hh := hper (T+m*P+r) (by omega)
        rw [hnext]
        simpa only [show T+m*P+P+r=T+m*P+r+P by omega] using hh.symm
      have hrow : ∀ p : Int, 1 ≤ p → p ≤ (2*K+1:Nat) →
          cell (T+m*P) p = cell (T+(m+1)*P) p := by
        intro p hp1 hpK
        rw [hstripe m hm p hp1 (by omega),hstripe (m+1) (by omega) p hp1 (by omega)]
      exact (cone_agree (T+m*P) (T+(m+1)*P) (2*K+1) hdriver hrow
        s 1 (by omega) (by omega)).symm
    · rw [(hcapture m (by omega)).1 s (by omega) (by omega),
        (hcapture (m+1) (by omega)).1 s (by omega) (by omega)]
  have hcol := phase_periodic (fun t => cell t 1) T P hP hphase
  exact not_adjacent 0 ⟨T,P,hP,hper⟩ ⟨T+2*P,P,hP,hcol⟩

end CedarPaddingExclusion
