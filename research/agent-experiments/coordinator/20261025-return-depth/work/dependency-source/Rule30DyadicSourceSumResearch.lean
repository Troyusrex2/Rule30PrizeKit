module
public import Rule30SourceSeriesResearch
public import Rule30LucasMaskResearch

/-! Uniform shallow-source parity in the actual Rule30 source expansion.
The unbounded-depth remainder is not controlled, and Problem1 is not proved. -/
@[expose] public section
namespace Rule30DyadicSourceSumResearch
open Ruliology.CellularAutomata PowerSeries Finset
open Rule30SourceSeriesResearch Rule30DyadicSourceResearch

noncomputable def term (e s d : Nat) : ZMod 2 :=
  (if 2 ∣ 2*(2^e)-2-d then
    ((2*(2^e)-2-s).choose ((2*(2^e)-2-d)/2) : ZMod 2) else 0) * bit (source d s)

theorem cast_ne_zero_mod_two (a : Nat) (ha : (a : ZMod 2)≠0) : a%2=1 := by
  have hn : a%2≠0 := by
    intro hz
    exact ha ((ZMod.natCast_eq_zero_iff a 2).mpr (Nat.dvd_of_mod_eq_zero hz))
  have hl := Nat.mod_lt a (by omega : 0<2)
  omega

theorem shallow_term_eq (e s d : Nat) (hd : d≤e) (hs : s<2*(2^e)-1) :
    term e s d = if d=0 ∧ s=2^e-1 then 1 else 0 := by
  let H := 2^e
  have hH : 0<H := Nat.two_pow_pos e
  have hEH : e<H := Nat.lt_two_pow_self
  have hdM : d≤2*H-2 := by omega
  by_cases ho : d=0 ∧ s=H-1
  · rcases ho with ⟨rfl,rfl⟩
    have hhalf : (2*H-2)/2=H-1 := by omega
    have ht : 2*H-2-(H-1)=H-1 := by omega
    have heven : 2 ∣ 2*H-2 := by exact ⟨H-1,by omega⟩
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
        · have hp' := hp
          obtain ⟨q,hq⟩ := hp'
          have hdEven : d%2=0 := by omega
          have hdiv : (2*H-2-d)/2=H-1-d/2 := by omega
          have hm := Rule30LucasMaskResearch.choose_odd_submask
            (2*H-2-s) ((2*H-2-d)/2) (cast_ne_zero_mod_two _ hc)
          rw [hdiv] at hm
          have event : SelectedEvent e d s := ⟨hs,hdEven,hm,hb⟩
          exact (ho ((selected_event_iff_outer e d s hd).mp event)).elim
    · simp [term,show 2^e=H from rfl,hp]

theorem shallow_sum (e : Nat) :
    (∑ s ∈ range (2*(2^e)-1), ∑ d ∈ range (e+1), term e s d)=1 := by
  have hp := Nat.two_pow_pos e
  rw [Finset.sum_eq_single (2^e-1)]
  · rw [Finset.sum_eq_single 0]
    · rw [shallow_term_eq e (2^e-1) 0 (by omega) (by omega)]
      simp
    · intro d hd hne
      rw [shallow_term_eq e (2^e-1) d (by have := mem_range.mp hd; omega) (by omega)]
      simp [hne]
    · simp
  · intro s hs hne
    apply Finset.sum_eq_zero
    intro d hd
    rw [shallow_term_eq e s d (by have := mem_range.mp hd; omega) (mem_range.mp hs)]
    simp [hne]
  · intro hnot
    exact (hnot (mem_range.mpr (by omega))).elim

theorem dyadic_linear_zero (e : Nat) :
    PowerSeries.coeff (2*(2^e)-1) (A^(2*(2^e)-1))=0 := by
  rw [kernel_coeff,ite_eq_right]
  intro h
  obtain ⟨q,hq⟩ := h
  have hp := Nat.two_pow_pos e
  omega

theorem center_dyadic_total (e : Nat) :
    bit (Rule30Prize.center (2*(2^e)-1))=
      ∑ s ∈ range (2*(2^e)-1), ∑ d ∈ range (2*(2^e)-1), term e s d := by
  have hp := Nat.two_pow_pos e
  have hn : 2*(2^e)-2+1=2*(2^e)-1 := by omega
  have h := center_source_sum (2*(2^e)-2)
  rw [hn,dyadic_linear_zero,zero_add] at h
  exact h

/-- The actual center equals the unique shallow contribution 1 plus the
complete, unrestricted deep-source remainder. No eventual-period conclusion. -/
theorem center_eq_one_add_deep_sources (e : Nat) :
    bit (Rule30Prize.center (2*(2^e)-1))=1+
      ∑ s ∈ range (2*(2^e)-1), ∑ d ∈ Ico (e+1) (2*(2^e)-1), term e s d := by
  have hp := Nat.two_pow_pos e
  have he : e<2^e := Nat.lt_two_pow_self
  have hb : e+1≤2*(2^e)-1 := by omega
  rw [center_dyadic_total]
  have hsplit : ∀ s, (∑ d ∈ range (2*(2^e)-1),term e s d) =
      (∑ d ∈ range (e+1),term e s d)+∑ d ∈ Ico (e+1) (2*(2^e)-1),term e s d := by
    intro s
    exact (Finset.sum_range_add_sum_Ico (fun d => term e s d) hb).symm
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib,shallow_sum]

end Rule30DyadicSourceSumResearch
