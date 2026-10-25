module
public import Rule30ReturnSourcesResearch
public import Rule30DyadicSourceSumResearch

/-! The complete actual center-source sum localized beyond the actual
least-unreturned bit. The remaining higher-depth sum is unrestricted. -/
@[expose] public section
namespace Rule30ReturnSumResearch
open Ruliology.CellularAutomata PowerSeries Finset
open Rule30SourceSeriesResearch Rule30DyadicSourceResearch
open Rule30DyadicSourceSumResearch Rule30ReturnDepthResearch Rule30ReturnSourcesResearch

noncomputable def depth (e : Nat) : Nat := cut (2^e) (Nat.two_pow_pos e)

theorem depth_pos (e : Nat) : 0<depth e := cut_pos _ _
theorem depth_bound (e : Nat) : depth e≤2*(2^e)-1 := cut_bound _ _

theorem returned_term_eq (e s d : Nat) (hd : d<depth e) (hs : s<2*(2^e)-1) :
    term e s d=if d=0 ∧ s=2^e-1 then 1 else 0 := by
  let H := 2^e
  have hH : 0<H := Nat.two_pow_pos e
  have hb := depth_bound e
  have hdM : d≤2*H-2 := by omega
  by_cases ho : d=0 ∧ s=H-1
  · rcases ho with ⟨rfl,rfl⟩
    have hhalf : (2*H-2)/2=H-1 := by omega
    have ht : 2*H-2-(H-1)=H-1 := by omega
    have heven : 2 ∣ 2*H-2 := ⟨H-1,by omega⟩
    simp [term,show 2^e=H from rfl,heven,ht,hhalf,source_outer,bit]
  · have hout : ¬(d=0 ∧ s=2^e-1) := ho
    rw [ite_eq_right hout]
    by_cases hp : 2 ∣ 2*H-2-d
    · change (if 2 ∣ 2*H-2-d then
          ((2*H-2-s).choose ((2*H-2-d)/2) : ZMod 2) else 0) * bit (source d s)=0
      rw [ite_eq_left hp]
      by_cases hz : source d s=false
      · simp [hz,bit]
      · have hb : source d s=true := by cases h : source d s <;> simp_all
        by_cases hc : ((2*H-2-s).choose ((2*H-2-d)/2) : ZMod 2)=0
        · simp [hc]
        · obtain ⟨q,hq⟩ := hp
          have hdEven : d%2=0 := by omega
          have hdiv : (2*H-2-d)/2=H-1-d/2 := by omega
          have hm := Rule30LucasMaskResearch.choose_odd_submask
            (2*H-2-s) ((2*H-2-d)/2) (cast_ne_zero_mod_two _ hc)
          rw [hdiv] at hm
          have event : SelectedEvent e d s := ⟨hs,hdEven,hm,hb⟩
          exact (ho ((selected_event_iff_below_cut e d s hd).mp event)).elim
    · simp [term,show 2^e=H from rfl,hp]

theorem returned_sum (e : Nat) :
    (∑ s ∈ range (2*(2^e)-1),∑ d ∈ range (depth e),term e s d)=1 := by
  have hp := Nat.two_pow_pos e
  have hd := depth_pos e
  rw [Finset.sum_eq_single (2^e-1)]
  · rw [Finset.sum_eq_single 0]
    · rw [returned_term_eq e (2^e-1) 0 hd (by omega)]
      simp
    · intro d hd hne
      rw [returned_term_eq e (2^e-1) d (mem_range.mp hd) (by omega)]
      simp [hne]
    · simp [show 0<depth e from hd]
  · intro s hs hne
    apply Finset.sum_eq_zero
    intro d hd
    rw [returned_term_eq e s d (mem_range.mp hd) (mem_range.mp hs)]
    simp [hne]
  · intro hnot
    exact (hnot (mem_range.mpr (by omega))).elim

theorem center_eq_one_add_after_return (e : Nat) :
    bit (Rule30Prize.center (2*(2^e)-1))=1+
      ∑ s ∈ range (2*(2^e)-1),∑ d ∈ Ico (depth e) (2*(2^e)-1),term e s d := by
  rw [center_dyadic_total]
  have hs : ∀ s, (∑ d ∈ range (2*(2^e)-1),term e s d)=
      (∑ d ∈ range (depth e),term e s d)+
        ∑ d ∈ Ico (depth e) (2*(2^e)-1),term e s d := by
    intro s
    exact (Finset.sum_range_add_sum_Ico (fun d=>term e s d) (depth_bound e)).symm
  simp_rw [hs]
  rw [Finset.sum_add_distrib,returned_sum]

end Rule30ReturnSumResearch
