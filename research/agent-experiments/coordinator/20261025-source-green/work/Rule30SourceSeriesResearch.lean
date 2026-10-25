module
public import Rule30DyadicSourceResearch
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! The actual seed row and run-boundary sources in the moving right-edge
frame. This file proves an exact source expansion, not nonperiodicity. -/
@[expose] public section
namespace Rule30SourceSeriesResearch
open Ruliology.CellularAutomata Rule30Diagonals
open PowerSeries Finset

def bit (b : Bool) : ZMod 2 := if b then 1 else 0
noncomputable def row (t : Nat) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun d => bit (R d t)
noncomputable def sources (t : Nat) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun d => bit (Rule30DyadicSourceResearch.source d t)
noncomputable def A : PowerSeries (ZMod 2) := 1+X^2

theorem bit_xor (a b : Bool) : bit (xor a b)=bit a+bit b := by
  cases a <;> cases b <;> decide

theorem bit_or_source (a b : Bool) : bit (a || b)=bit b+bit (a && !b) := by
  cases a <;> cases b <;> decide

theorem row_zero : row 0=1 := by
  ext d
  cases d with
  | zero => simp [row,R,Rule30Jen.cell,bit]
  | succ d => simp [row,Rule30DyadicSourceResearch.R_at_zero (d+1) (by omega),bit]

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
      have hs : Rule30DyadicSourceResearch.source 0 t=true := Rule30DyadicSourceResearch.source_outer t
      simp only [hs]
      cases R 1 t <;> norm_num [bit]
      all_goals decide
    | succ d =>
      simp only [map_add,coeff_succ_X_mul,row,sources,coeff_mk]
      rw [R_step,bit_xor,bit_or_source]
      simp [Rule30DyadicSourceResearch.source,add_assoc]

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
          bit (Rule30DyadicSourceResearch.source d s) := by
  rw [show A^h*(X*sources s)=X*(sources s*A^h) by ring,
    coeff_succ_X_mul,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [sources,kernel_coeff,mul_comm]

theorem center_source_sum (m : Nat) : bit (Rule30Prize.center (m+1))=
    PowerSeries.coeff (m+1) (A^(m+1))+
      ∑ s ∈ range (m+1), ∑ d ∈ range (m+1),
        (if 2 ∣ m-d then ((m-s).choose ((m-d)/2) : ZMod 2) else 0) *
          bit (Rule30DyadicSourceResearch.source d s) := by
  rw [center_duhamel]
  simp [source_convolution]

end Rule30SourceSeriesResearch
