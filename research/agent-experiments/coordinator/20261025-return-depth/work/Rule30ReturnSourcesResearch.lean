module
public import Rule30ReturnDepthResearch

/-! Actual return-depth localization of the source mask. This improves the
cutoff to the least unreturned bit, but does not control the complete tail. -/
@[expose] public section
namespace Rule30ReturnSourcesResearch
open Ruliology.CellularAutomata Rule30Diagonals Rule30DyadicSourceResearch
open Rule30ReturnDepthResearch

theorem mask_times (e r s : Nat) (hr : r<2^e) (hs : s<2*(2^e)-1)
    (hk : ((2^e-1-r) &&& (2*(2^e)-2-s))=2^e-1-r) :
    s<r ∨ s=2^e-1 ∨ (2^e≤s ∧ s<2^e+r) := by
  let H := 2^e
  have hH : 0<H := Nat.two_pow_pos e
  have hK : H-1-r<H := by omega
  have hmod := congrArg (fun x => x%H) hk
  change ((H-1-r) &&& (2*H-2-s))%H=(H-1-r)%H at hmod
  rw [Nat.and_mod_two_pow,Nat.mod_eq_of_lt hK] at hmod
  have hb : H-1-r≤(2*H-2-s)%H := by rw [←hmod]; exact Nat.and_le_right
  by_cases hearly : s<r
  · exact Or.inl hearly
  have hleft : H-1≤s := by
    by_cases h : H-1≤s
    · exact h
    · have hhi : H≤2*H-2-s := by omega
      have hm : (2*H-2-s)%H=(2*H-2-s)-H := by
        rw [Nat.mod_eq_sub_mod hhi,Nat.mod_eq_of_lt (by omega)]
      rw [hm] at hb
      omega
  have hright : s<H+r := by
    rw [Nat.mod_eq_of_lt (show 2*H-2-s<H by omega)] at hb
    omega
  by_cases hlast : s=H-1
  · exact Or.inr (Or.inl hlast)
  · exact Or.inr (Or.inr ⟨by omega,hright⟩)

theorem cut_exceeds_exponent (e : Nat) : e<cut (2^e) (Nat.two_pow_pos e) := by
  by_cases h : e<cut (2^e) (Nat.two_pow_pos e)
  · exact h
  · have hc : cut (2^e) (Nat.two_pow_pos e)≤e := by omega
    have heq := R_period_pow (cut (2^e) (Nat.two_pow_pos e)) e hc 0
    have hn := cut_changed (2^e) (Nat.two_pow_pos e)
    apply False.elim
    apply hn
    simpa using heq

theorem source_zero_below_cut (e r s : Nat) (hr : 0<r)
    (hc : 2*r<cut (2^e) (Nat.two_pow_pos e)) (hs : s<2*(2^e)-1)
    (hk : ((2^e-1-r) &&& (2*(2^e)-2-s))=2^e-1-r) : source (2*r) s=false := by
  have hp := Nat.two_pow_pos e
  have hb := cut_bound (2^e) hp
  have hrH : r<2^e := by omega
  rcases mask_times e r s hrH hs hk with hearly | hlast | hlate
  · exact source_zero_before_cone _ _ (by omega)
  · rw [hlast]
    exact source_prefix_last _ hp _ (by omega) hc
  · have ht : s=2^e+(s-2^e) := by omega
    rw [ht]
    exact source_prefix_window _ hp _ _ hc (by omega)

/-- Within the entire returned prefix, the only actual nonzero source
selected by the mask is still the single outer event. -/
theorem selected_event_iff_below_cut (e d s : Nat)
    (hd : d<cut (2^e) (Nat.two_pow_pos e)) :
    SelectedEvent e d s ↔ d=0 ∧ s=2^e-1 := by
  constructor
  · rintro ⟨hs,heven,hmask,hsource⟩
    by_cases hz : d=0
    · refine ⟨hz,?_⟩
      subst d
      simp only [Nat.zero_div,Nat.sub_zero] at hmask
      exact (outer_kernel_iff e s hs).mp hmask
    · have heq : d=2*(d/2) := by omega
      have hzero := source_zero_below_cut e (d/2) s (by omega) (by omega) hs hmask
      rw [←heq,hsource] at hzero
      contradiction
  · rintro ⟨rfl,rfl⟩
    have hp := Nat.two_pow_pos e
    refine ⟨by omega,by omega,?_,source_outer _⟩
    simp only [Nat.zero_div,Nat.sub_zero]
    exact (outer_kernel_iff e (2^e-1) (by omega)).mpr rfl

/-- At an even least-unreturned depth, each selected source is known
pointwise: zero before H and one in the permitted window after H. This
does not evaluate the complete source sum. -/
theorem cut_layer_source (e r s : Nat)
    (hc : cut (2^e) (Nat.two_pow_pos e)=2*r) (hs : s<2*(2^e)-1)
    (hk : ((2^e-1-r) &&& (2*(2^e)-2-s))=2^e-1-r) :
    source (2*r) s=decide (2^e≤s) := by
  have hp := Nat.two_pow_pos e
  have hpos := cut_pos (2^e) hp
  have hb := cut_bound (2^e) hp
  have hr : 0<r := by omega
  have hrH : r<2^e := by omega
  rcases mask_times e r s hrH hs hk with hearly | hlast | hlate
  · rw [source_zero_before_cone _ _ (by omega),decide_eq_false (by omega)]
  · rw [hlast,←hc,source_cut_last _ hp,decide_eq_false (by omega)]
  · rw [show s=2^e+(s-2^e) by omega,←hc,source_cut_window _ hp _ (by omega)]
    simp [show 2^e≤2^e+(s-2^e) by omega]

end Rule30ReturnSourcesResearch
