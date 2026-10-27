module

public import Ruliology.CellularAutomata.Rule30RunBoundarySources
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# The center as a sum of deeper run-boundary sources

In the moving right-edge coordinate, depth `d` at time `s` is the physical cell
`cell s (s-d)`. The source `Rule30RunBoundarySources.source d s` marks a black cell
whose right neighbor is white. Over `𝔽₂`, Rule 30 is Rule 90 plus this source.
Consequently the row series satisfies `row (s+1) = (1+X²) * row s + X * sources s`.

* `center_source_sum` unrolls this recurrence for every positive time. Its kernel
  is the Rule 90 binomial coefficient, with odd spatial displacements omitted.
* `choose_odd_submask` obtains the binary support of that coefficient from Lucas'
  theorem. `shallow_term_eq` then applies
  `Rule30RunBoundarySources.selected_event_iff_outer` to the actual sources.
* `center_eq_one_add_deep_sources`: for every `e`, put `H = 2^e` and `n = 2H-1`.
  The center at time `n` is `1` plus the complete source sum over times `s < n`
  and depths `e+1 ≤ d < n`. The linear term vanishes, and the omitted shallow
  strip contributes exactly the outer source at `d = 0`, `s = H-1`.
  This includes `e = 0`, when the deeper range is empty.

`Rule30Diagonals.center_eq_parity` telescopes one right diagonal: it counts earlier
ORs of the two preceding diagonals. Here the linear Rule 90 part is propagated
across all source depths, producing a two-dimensional time/depth sum, and Lucas'
theorem removes its shallow strip at dyadic times. The deeper remainder is left
unrestricted. This differs also from `CenterFormulas.center_duhamel`, whose linear
part is Rule 150 and whose nonlinear source is a product of adjacent black cells.
-/

@[expose] public section

namespace Rule30Equivalents.DyadicSources

open Ruliology.CellularAutomata Rule30Diagonals Rule30RunBoundarySources
open PowerSeries Finset

def bit (b : Bool) : ZMod 2 := if b then 1 else 0
noncomputable def row (t : Nat) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun d => bit (R d t)
noncomputable def sources (t : Nat) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun d => bit (Rule30RunBoundarySources.source d t)
noncomputable def A : PowerSeries (ZMod 2) := 1+X^2

theorem bit_xor (a b : Bool) : bit (xor a b)=bit a+bit b := by
  cases a <;> cases b <;> decide

theorem bit_or_source (a b : Bool) : bit (a || b)=bit b+bit (a && !b) := by
  cases a <;> cases b <;> decide

theorem row_zero : row 0=1 := by
  ext d
  cases d with
  | zero => simp [row,R,Rule30Jen.cell,bit]
  | succ d => simp [row,Rule30RunBoundarySources.R_at_zero (d+1) (by omega),bit]

theorem row_succ (t : Nat) : row (t+1)=A*row t+X*sources t := by
  rw [A,add_mul,one_mul,pow_two,mul_assoc]
  ext d
  cases d with
  | zero => simp [row,sources,R_zero,bit]
  | succ d =>
    cases d with
    | zero =>
      simp only [map_add,coeff_succ_X_mul,coeff_mk,row,sources]
      rw [R_one_succ]
      have hs : Rule30RunBoundarySources.source 0 t=true := Rule30RunBoundarySources.source_outer t
      simp only [hs]
      cases R 1 t <;> norm_num [bit]
      all_goals decide
    | succ d =>
      simp only [map_add,coeff_succ_X_mul,row,sources,coeff_mk]
      rw [R_step,bit_xor,bit_or_source]
      simp [Rule30RunBoundarySources.source,add_assoc]

theorem duhamel : ∀ n : Nat, row n=A^n+
    ∑ s ∈ range n, A^(n-1-s)*(X*sources s)
  | 0 => by simp [row_zero]
  | n+1 => by
    rw [row_succ,duhamel n,mul_add,mul_sum,sum_range_succ]
    rw [show n+1-1-n=0 by omega,pow_zero,one_mul,←pow_succ']
    have hs : (∑ s ∈ range n, A*(A^(n-1-s)*(X*sources s))) =
        ∑ s ∈ range n, A^(n+1-1-s)*(X*sources s) := by
      apply sum_congr rfl
      intro s hs
      rw [←mul_assoc,←pow_succ',show n-1-s+1=n+1-1-s by have := mem_range.mp hs; omega]
    rw [hs,add_assoc]

theorem coeff_center (n : Nat) : PowerSeries.coeff n (row n)=bit (Rule30Prize.center n) := by
  simp [row,Rule30Prize.center,R]

theorem center_duhamel (n : Nat) : bit (Rule30Prize.center n)=
    PowerSeries.coeff n (A^n)+∑ s ∈ range n,
      PowerSeries.coeff n (A^(n-1-s)*(X*sources s)) := by
  rw [←coeff_center,duhamel,map_add,map_sum]

theorem coeff_binomial (h k : Nat) :
    PowerSeries.coeff k ((1+X)^h : PowerSeries (ZMod 2)) = (h.choose k : ZMod 2) := by
  have he : ((1+X)^h : PowerSeries (ZMod 2)) =
      (((1+Polynomial.X)^h : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) := by simp
  rw [he,Polynomial.coeff_coe,Polynomial.coeff_one_add_X_pow]

theorem kernel_coeff (h k : Nat) : PowerSeries.coeff k (A^h)=
    if 2 ∣ k then (h.choose (k/2) : ZMod 2) else 0 := by
  have he : A^h=PowerSeries.expand 2 (by decide) ((1+X)^h : PowerSeries (ZMod 2)) := by
    simp [A,map_pow,map_add,PowerSeries.expand_X]
  rw [he,PowerSeries.coeff_expand,coeff_binomial]

theorem source_convolution (m h s : Nat) :
    PowerSeries.coeff (m+1) (A^h*(X*sources s))=
      ∑ d ∈ range (m+1),
        (if 2 ∣ m-d then (h.choose ((m-d)/2) : ZMod 2) else 0) *
          bit (Rule30RunBoundarySources.source d s) := by
  rw [show A^h*(X*sources s)=X*(sources s*A^h) by ring,
    coeff_succ_X_mul,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [sources,kernel_coeff,mul_comm]

theorem center_source_sum (m : Nat) : bit (Rule30Prize.center (m+1))=
    PowerSeries.coeff (m+1) (A^(m+1))+
      ∑ s ∈ range (m+1), ∑ d ∈ range (m+1),
        (if 2 ∣ m-d then ((m-s).choose ((m-d)/2) : ZMod 2) else 0) *
          bit (Rule30RunBoundarySources.source d s) := by
  rw [center_duhamel]
  simp [source_convolution]


theorem choose_odd_submask (n k : Nat) (hc : n.choose k % 2=1) : k &&& n=k := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    by_cases hn : n=0
    · subst n
      by_cases hk : k=0
      · subst k; rfl
      · have hz : Nat.choose 0 k=0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hz] at hc
        contradiction
    have hdiv : n/2<n := Nat.div_lt_self (by omega) (by omega)
    have hluc : n.choose k % 2 =
        (Nat.choose (n%2) (k%2) * Nat.choose (n/2) (k/2))%2 :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=2)
    have hb : Nat.choose (n/2) (k/2)%2=1 := by
      by_cases hz : Nat.choose (n/2) (k/2)%2=0
      · rw [Nat.mul_mod,hz,Nat.mul_zero,Nat.zero_mod,hc] at hluc
        contradiction
      · have hlt := Nat.mod_lt (Nat.choose (n/2) (k/2)) (by omega : 0<2)
        omega
    have hi := ih (n/2) hdiv (k/2) hb
    have hlo : k%2≤n%2 := by
      have hkn := Nat.mod_lt k (by omega : 0<2)
      have hnn := Nat.mod_lt n (by omega : 0<2)
      by_cases hk0 : k%2=0
      · omega
      · have hk1 : k%2=1 := by omega
        by_cases hn0 : n%2=0
        · simp [hn0,hk1,hc] at hluc
        · omega
    have hquot : (k &&& n)/2=k/2 := by rw [Nat.and_div_two,hi]
    have hrem : (k &&& n)%2=k%2 := by
      have hm : (k &&& n)%2=(k%2) &&& (n%2) := Nat.and_mod_two_pow (n:=1)
      rw [hm]
      have hklt := Nat.mod_lt k (by omega : 0<2)
      have hnlt := Nat.mod_lt n (by omega : 0<2)
      by_cases hk0 : k%2=0
      · simp [hk0]
      · have hk1 : k%2=1 := by omega
        have hn1 : n%2=1 := by omega
        simp [hk1,hn1]
    have ha := Nat.mod_add_div (k &&& n) 2
    have hk := Nat.mod_add_div k 2
    omega


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
          have hm := choose_odd_submask
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
complete, unrestricted deep-source remainder. -/
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


end Rule30Equivalents.DyadicSources
