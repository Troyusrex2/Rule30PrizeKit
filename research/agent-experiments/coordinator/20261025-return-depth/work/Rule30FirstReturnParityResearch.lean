module
public import Rule30ReturnSumResearch
public import Mathlib.Data.Nat.Choose.Sum

/-! The first interior channel at an even actual return depth has odd
parity. It cancels the outer 1; it does not settle the higher-depth sum. -/
@[expose] public section
namespace Rule30FirstReturnParityResearch
open Ruliology.CellularAutomata PowerSeries Finset
open Rule30SourceSeriesResearch Rule30DyadicSourceResearch Rule30DyadicSourceSumResearch
open Rule30ReturnDepthResearch Rule30ReturnSourcesResearch Rule30ReturnSumResearch

theorem all_ones_choose (e k : Nat) (hk : k<2^e) :
    ((2^e-1).choose k : ZMod 2)=1 := by
  induction e generalizing k with
  | zero =>
    have hz : k=0 := by simpa using hk
    subst k
    decide
  | succ e ih =>
    have hp := Nat.two_pow_pos e
    have hpow : 2^(e+1)=2*(2^e) := by rw [Nat.pow_succ]; omega
    have hm : (2^(e+1)-1)%2=1 := by omega
    have hd : (2^(e+1)-1)/2=2^e-1 := by omega
    have hlow : Nat.choose 1 (k%2)=1 := by
      have hb := Nat.mod_lt k (by omega : 0<2)
      by_cases h : k%2=0
      · simp [h]
      · have : k%2=1 := by omega
        simp [this]
    have hmod : (2^(e+1)-1).choose k %2 =
        (Nat.choose ((2^(e+1)-1)%2) (k%2) * Nat.choose ((2^(e+1)-1)/2) (k/2))%2 :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=2)
    have heq : ((2^(e+1)-1).choose k : ZMod 2)=
        ((Nat.choose ((2^(e+1)-1)%2) (k%2) * Nat.choose ((2^(e+1)-1)/2) (k/2) : Nat) : ZMod 2) :=
      (ZMod.natCast_eq_natCast_iff' _ _ 2).mpr hmod
    rw [heq,Nat.cast_mul,hm,hd,hlow,Nat.cast_one,one_mul]
    exact ih (k/2) (by omega)

theorem first_layer_term (e r s : Nat) (hc : depth e=2*r) (hs : s<2*(2^e)-1) :
    term e s (2*r)=if 2^e≤s ∧ s<2^e+r then
      ((2*(2^e)-2-s).choose (2^e-1-r) : ZMod 2) else 0 := by
  let H := 2^e
  have hp : 0<H := Nat.two_pow_pos e
  have hpos := depth_pos e
  have hbound := depth_bound e
  have hr : 0<r := by omega
  have hrH : r<H := by omega
  have hm : (2*H-2-2*r)/2=H-1-r := by omega
  have heven : 2 ∣ 2*H-2-2*r := ⟨H-1-r,by omega⟩
  change (if 2 ∣ 2*H-2-2*r then
      ((2*H-2-s).choose ((2*H-2-2*r)/2) : ZMod 2) else 0)*bit (source (2*r) s)=_
  rw [ite_eq_left heven,hm]
  by_cases hz : ((2*H-2-s).choose (H-1-r) : ZMod 2)=0
  · simp [hz,show 2^e=H from rfl]
  · have hk := Rule30LucasMaskResearch.choose_odd_submask
      (2*H-2-s) (H-1-r) (cast_ne_zero_mod_two _ hz)
    have hb := cut_layer_source e r s hc hs hk
    rw [hb]
    have ht := mask_times e r s hrH hs hk
    by_cases hlate : H≤s
    · have htime : H≤s ∧ s<H+r := by rcases ht with h|h|h <;> omega
      simp [bit,hlate,htime,show 2^e=H from rfl]
    · simp [bit,hlate,show 2^e=H from rfl]

theorem first_even_channel_odd (e r : Nat) (hc : depth e=2*r) :
    (∑ s ∈ range (2*(2^e)-1),term e s (2*r))=1 := by
  let H := 2^e
  let K := H-1-r
  have hp : 0<H := Nat.two_pow_pos e
  have hpos := depth_pos e
  have hbound := depth_bound e
  have hr : 0<r := by omega
  have hrH : r<H := by omega
  have hsubset : (Ico H (H+r) : Finset Nat) ⊆ range (2*H-1) := by
    intro s hs
    simp only [mem_Ico,mem_range] at hs ⊢
    omega
  calc
    (∑ s ∈ range (2*(2^e)-1),term e s (2*r)) =
        ∑ s ∈ Ico H (H+r),term e s (2*r) := by
      apply (Finset.sum_subset hsubset ?_).symm
      intro s hs hnot
      rw [first_layer_term e r s hc (mem_range.mp hs),ite_eq_right]
      simpa only [mem_Ico] using hnot
    _ = ∑ s ∈ Ico H (H+r),((2*H-2-s).choose K : ZMod 2) := by
      apply sum_congr rfl
      intro s hs
      have ht := mem_Ico.mp hs
      rw [first_layer_term e r s hc (by have := hsubset hs; exact mem_range.mp this),ite_eq_left ht]
    _ = ∑ h ∈ Icc K (H-2),(h.choose K : ZMod 2) := by
      apply Finset.sum_bij (fun s _=>2*H-2-s)
      · intro s hs
        simp only [mem_Ico,mem_Icc] at hs ⊢
        dsimp [K]
        omega
      · intro s hs t ht heq
        simp only [mem_Ico] at hs ht
        omega
      · intro h hh
        simp only [mem_Icc] at hh
        refine ⟨2*H-2-h,?_,?_⟩
        · simp only [mem_Ico]
          dsimp [K] at hh
          omega
        · omega
      · intro s hs
        rfl
    _ = ((H-1).choose (K+1) : ZMod 2) := by
      rw [←Nat.cast_sum,Nat.sum_Icc_choose,show H-2+1=H-1 by omega]
    _ = 1 := all_ones_choose e (K+1) (by dsimp [K]; omega)

/-- At even return depth the first interior odd channel cancels the outer
one. The actual center is exactly the still-unrestricted higher remainder. -/
theorem center_after_even_return (e r : Nat) (hc : depth e=2*r) :
    bit (Rule30Prize.center (2*(2^e)-1))=
      ∑ s ∈ range (2*(2^e)-1),∑ d ∈ Ico (2*r+1) (2*(2^e)-1),term e s d := by
  have hpos := depth_pos e
  have hb := depth_bound e
  have hp := Nat.two_pow_pos e
  have hlt : 2*r<2*(2^e)-1 := by omega
  rw [center_eq_one_add_after_return,hc]
  have hs : ∀ s, (∑ d ∈ Ico (2*r) (2*(2^e)-1),term e s d)=
      term e s (2*r)+∑ d ∈ Ico (2*r+1) (2*(2^e)-1),term e s d := by
    intro s
    exact Finset.sum_eq_sum_Ico_succ_bot hlt (fun d=>term e s d)
  simp_rw [hs]
  rw [Finset.sum_add_distrib,first_even_channel_odd e r hc,←add_assoc]
  have h11 : (1:ZMod 2)+1=0 := by decide
  rw [h11,zero_add]

end Rule30FirstReturnParityResearch
