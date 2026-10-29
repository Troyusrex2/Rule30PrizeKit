module
public import Ruliology.CellularAutomata.Rule30Prize
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.Ring

/-! Research coordinates, not a nonperiodicity proof.
Classical binomial/Hankel identities are not claimed as new mathematics. -/
@[expose] public section
namespace NewtonHankel
open Finset Ruliology.CellularAutomata

def transform {R : Type*} [Semiring R] (f : Nat → R) (n : Nat) : R :=
  ∑ t ∈ range (n+1), (n.choose t : R)*f t

theorem transform_succ {R : Type*} [Semiring R] (f : Nat → R) (n : Nat) :
    transform f (n+1)=transform f n+transform (fun t => f (t+1)) n := by
  simpa only [transform] using sum_choose_succ_mul (fun i _ => f i) n

theorem transform_add {R : Type*} [Semiring R] (f g : Nat → R) (n : Nat) :
    transform (f+g) n=transform f n+transform g n := by
  simp only [transform,Pi.add_apply,mul_add,sum_add_distrib]

theorem transform_add_indices {R : Type*} [Semiring R] (f : Nat → R) (i j : Nat) :
    transform f (i+j)=transform (fun a => transform (fun t => f (a+t)) j) i := by
  induction i generalizing f with
  | zero => simp [transform]
  | succ i ih =>
    rw [show i+1+j=(i+j)+1 by omega,transform_succ,ih,ih,transform_succ]
    congr 1
    apply congrArg (fun g : Nat → R => transform g i)
    funext a
    apply congrArg (fun g : Nat → R => transform g j)
    funext t
    congr 1
    omega

theorem sum_fin_choose {R : Type*} [Semiring R] (g : Nat → R)
    (n i : Nat) (hi : i<n) :
    (∑ a : Fin n, (i.choose a.val : R)*g a.val)=transform g i := by
  change (∑ a : Fin n, (fun a : Nat => (i.choose a : R)*g a) a.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun a : Nat => (i.choose a : R)*g a) n]
  unfold transform
  symm
  apply sum_subset (range_mono (by omega : i+1≤n))
  intro a ha hnot
  have hia : i<a := by simp only [mem_range] at hnot;omega
  simp [Nat.choose_eq_zero_of_lt hia]

def hankel {R : Type*} (f : Nat → R) (n : Nat) : Matrix (Fin n) (Fin n) R :=
  fun i j => f (i.val+j.val)
def pascal (R : Type*) [Semiring R] (n : Nat) : Matrix (Fin n) (Fin n) R :=
  fun i j => (i.val.choose j.val : R)

/-- Classical Pascal congruence, in the exact coordinates used below. -/
theorem hankel_transform {R : Type*} [CommRing R] (f : Nat → R) (n : Nat) :
    hankel (transform f) n=pascal R n*hankel f n*(pascal R n).transpose := by
  ext i j
  change transform f (i.val+j.val)=_
  have he : (pascal R n*hankel f n*(pascal R n).transpose) i j=
      ∑ a : Fin n, (i.val.choose a.val : R)*
        (∑ b : Fin n, (j.val.choose b.val : R)*f (a.val+b.val)) := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply,pascal,hankel]
    simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    rw [mul_sum]
    apply sum_congr rfl
    intro b hb
    ring
  rw [he]
  have hin (a : Fin n) : (∑ b : Fin n, (j.val.choose b.val : R)*f (a.val+b.val))=
      transform (fun t => f (a.val+t)) j.val :=
    sum_fin_choose (fun t => f (a.val+t)) n j.val j.isLt
  simp_rw [hin]
  rw [sum_fin_choose (fun a => transform (fun t => f (a+t)) j.val) n i.val i.isLt]
  exact transform_add_indices f i.val j.val

theorem det_pascal (R : Type*) [CommRing R] (n : Nat) : (pascal R n).det=1 := by
  have hl : (pascal R n).IsLowerTriangular := by
    intro i j hij
    have hh : i.val<j.val := hij
    simp [pascal,Nat.choose_eq_zero_of_lt hh]
  rw [Matrix.det_of_isLowerTriangular _ hl]
  simp [pascal]

theorem det_hankel_transform {R : Type*} [CommRing R] (f : Nat → R) (n : Nat) :
    (hankel (transform f) n).det=(hankel f n).det := by
  rw [hankel_transform,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,det_pascal]
  simp

/-- Monomorphic headline for the official partial-result checker. -/
theorem det_hankel_transform_two (f : Nat → ZMod 2) (n : Nat) :
    (hankel (transform f) n).det=(hankel f n).det := det_hankel_transform f n

def bit (b : Bool) : ZMod 2 := if b then 1 else 0
def field (t : Nat) (p : Int) : ZMod 2 := bit (Rule30Jen.cell t p)
def newtonRow (n : Nat) (p : Int) : ZMod 2 := transform (fun t => field t p) n
def newtonSource (n : Nat) (p : Int) : ZMod 2 :=
  transform (fun t => field t p*field t (p+1)) n

theorem field_succ (t : Nat) (p : Int) : field (t+1) p=
    field t (p-1)+field t p+field t (p+1)+field t p*field t (p+1) := by
  unfold field
  change bit (Rule30Jen.rule _ _ _)=_
  generalize Rule30Jen.cell t (p-1)=a
  generalize Rule30Jen.cell t p=b
  generalize Rule30Jen.cell t (p+1)=c
  cases a <;> cases b <;> cases c <;> decide

theorem double_zero (a : ZMod 2) : a+a=0 := by
  have h : ∀ a : ZMod 2, a+a=0 := by decide
  exact h a

/-- In characteristic two the binomial transform is its own inverse. -/
theorem transform_involutive (f : Nat → ZMod 2) (n : Nat) :
    transform (transform f) n=f n := by
  induction n generalizing f with
  | zero => simp [transform]
  | succ n ih =>
    rw [transform_succ,ih]
    have he : (fun t => transform f (t+1))=
        transform f+transform (fun t => f (t+1)) := by
      funext t
      exact transform_succ f t
    rw [he,transform_add,ih,ih]
    calc
      _ = (f n+f n)+f (n+1) := by ring
      _ = _ := by rw [double_zero,zero_add]

theorem transform_succ_succ (f : Nat → ZMod 2) (n : Nat) :
    transform f (n+2)=transform f n+transform (fun t => f (t+2)) n := by
  rw [show n+2=(n+1)+1 by omega,transform_succ,transform_succ,transform_succ]
  have hs : (fun t => f (t+1+1))=(fun t => f (t+2)) := by
    funext t
    congr 1
  rw [hs]
  have hz := double_zero (transform (fun t => f (t+1)) n)
  calc
    _ = transform f n+(transform (fun t => f (t+1)) n+
      transform (fun t => f (t+1)) n)+transform (fun t => f (t+2)) n := by ring
    _ = _ := by rw [hz,add_zero]

/-- Exact dyadic decimation; no appeal to empirical kernel counts. -/
theorem transform_even (f : Nat → ZMod 2) (n : Nat) :
    transform f (2*n)=transform (fun t => f (2*t)) n := by
  induction n generalizing f with
  | zero => simp [transform]
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega,transform_succ_succ,ih,ih,transform_succ]
    congr 1

theorem transform_odd (f : Nat → ZMod 2) (n : Nat) :
    transform f (2*n+1)=transform (fun t => f (2*t)) n+
      transform (fun t => f (2*t+1)) n := by
  rw [transform_succ,transform_even,transform_even]

/-- Transport pointwise multiplication into the Newton coordinates. -/
def sourceProduct (f g : Nat → ZMod 2) (n : Nat) : ZMod 2 :=
  transform (fun t => transform f t*transform g t) n

theorem sourceProduct_zero (f g : Nat → ZMod 2) :
    sourceProduct f g 0=f 0*g 0 := by simp [sourceProduct,transform]

theorem sourceProduct_add_right (f g h : Nat → ZMod 2) (n : Nat) :
    sourceProduct f (g+h) n=sourceProduct f g n+sourceProduct f h n := by
  unfold sourceProduct
  have he : (fun t => transform f t*transform (g+h) t)=
      (fun t => transform f t*transform g t)+(fun t => transform f t*transform h t) := by
    funext t
    simp only [transform_add,Pi.add_apply,mul_add]
  rw [he,transform_add]

def spike (n : Nat) : Nat → ZMod 2 := fun t => if t=n then 1 else 0

theorem transform_spike_prefix (n t : Nat) (h : t≤n) :
    transform (spike n) t=spike n t := by
  unfold transform
  by_cases ht : t=n
  · subst t
    simp [spike]
  · have htn : t<n := by omega
    have hz : ∑ a ∈ range (t+1), (t.choose a : ZMod 2)*spike n a=0 := by
      apply sum_eq_zero
      intro a ha
      have han : a≠n := by simp only [mem_range] at ha;omega
      simp [spike,han]
    rw [hz]
    simp [spike,ht]

theorem sourceProduct_spike_right (f : Nat → ZMod 2) (n : Nat) :
    sourceProduct f (spike n) n=transform f n := by
  change (∑ t ∈ range (n+1), (n.choose t : ZMod 2)*
    (transform f t*transform (spike n) t))=transform f n
  have he : (∑ t ∈ range (n+1), (n.choose t : ZMod 2)*
      (transform f t*transform (spike n) t))=
      ∑ t ∈ range (n+1), (n.choose t : ZMod 2)*(transform f t*spike n t) := by
    apply sum_congr rfl
    intro t ht
    have htn : t≤n := by simp only [mem_range] at ht;omega
    rw [transform_spike_prefix n t htn]
  rw [he]
  simp [spike,transform]

/-- The newest Newton-coordinate neighbor is still masked by the actual center.
This is an algebraic sensitivity statement, not a free variation of the seed. -/
theorem newest_neighbor_still_masked (f g : Nat → ZMod 2) (n : Nat) :
    (g+spike n) n+sourceProduct f (g+spike n) n=
      (g n+sourceProduct f g n)+(1+transform f n) := by
  rw [sourceProduct_add_right,sourceProduct_spike_right]
  simp only [Pi.add_apply,spike,ite_true]
  ring

/-- A uniform exact recursion. It does not assert that any summand survives. -/
theorem sourceProduct_succ (f g : Nat → ZMod 2) (n : Nat) :
    sourceProduct f g (n+1)=
      sourceProduct f (fun t => g (t+1)) n+
      sourceProduct (fun t => f (t+1)) g n+
      sourceProduct (fun t => f (t+1)) (fun t => g (t+1)) n := by
  unfold sourceProduct
  rw [transform_succ]
  have he : (fun t => transform f (t+1)*transform g (t+1))=
      (fun t => transform f t*transform g t)+
      (fun t => transform f t*transform (fun s => g (s+1)) t)+
      (fun t => transform (fun s => f (s+1)) t*transform g t)+
      (fun t => transform (fun s => f (s+1)) t*transform (fun s => g (s+1)) t) := by
    funext t
    simp only [transform_succ,Pi.add_apply]
    ring
  rw [he]
  simp only [transform_add]
  have hx := double_zero (transform (fun t => transform f t*transform g t) n)
  calc
    _ = (transform (fun t => transform f t*transform g t) n+
        transform (fun t => transform f t*transform g t) n)+
      (transform (fun t => transform f t*transform (fun s => g (s+1)) t) n+
        transform (fun t => transform (fun s => f (s+1)) t*transform g t) n+
        transform (fun t => transform (fun s => f (s+1)) t*
          transform (fun s => g (s+1)) t) n) := by ring
    _ = _ := by rw [hx,zero_add]

theorem actual_sourceProduct (n : Nat) (p : Int) :
    newtonSource n p=sourceProduct (fun t => newtonRow t p)
      (fun t => newtonRow t (p+1)) n := by
  simp only [newtonSource,newtonRow,sourceProduct,transform_involutive]

theorem sourceProduct_even (f g : Nat → ZMod 2) (n : Nat) :
    sourceProduct f g (2*n)=
      sourceProduct (fun t => f (2*t)) (fun t => g (2*t)) n := by
  unfold sourceProduct
  rw [transform_even]
  simp only [transform_even]

theorem sourceProduct_odd (f g : Nat → ZMod 2) (n : Nat) :
    sourceProduct f g (2*n+1)=
      sourceProduct (fun t => f (2*t)) (fun t => g (2*t+1)) n+
      sourceProduct (fun t => f (2*t+1)) (fun t => g (2*t)) n+
      sourceProduct (fun t => f (2*t+1)) (fun t => g (2*t+1)) n := by
  unfold sourceProduct
  rw [transform_odd]
  simp only [transform_even,transform_odd]
  have he : (fun t =>
      (transform (fun s => f (2*s)) t+transform (fun s => f (2*s+1)) t)*
      (transform (fun s => g (2*s)) t+transform (fun s => g (2*s+1)) t))=
      (fun t => transform (fun s => f (2*s)) t*transform (fun s => g (2*s)) t)+
      (fun t => transform (fun s => f (2*s)) t*transform (fun s => g (2*s+1)) t)+
      (fun t => transform (fun s => f (2*s+1)) t*transform (fun s => g (2*s)) t)+
      (fun t => transform (fun s => f (2*s+1)) t*transform (fun s => g (2*s+1)) t) := by
    funext t
    simp only [Pi.add_apply]
    ring
  rw [he]
  simp only [transform_add]
  have hz := double_zero (transform (fun t =>
    transform (fun s => f (2*s)) t*transform (fun s => g (2*s)) t) n)
  calc
    _ = (transform (fun t => transform (fun s => f (2*s)) t*
        transform (fun s => g (2*s)) t) n+
        transform (fun t => transform (fun s => f (2*s)) t*
        transform (fun s => g (2*s)) t) n)+
      (transform (fun t => transform (fun s => f (2*s)) t*
        transform (fun s => g (2*s+1)) t) n+
      transform (fun t => transform (fun s => f (2*s+1)) t*
        transform (fun s => g (2*s)) t) n+
      transform (fun t => transform (fun s => f (2*s+1)) t*
        transform (fun s => g (2*s+1)) t) n) := by ring
    _ = _ := by rw [hz,zero_add]

/-- The exact transformed dynamics has Rule90 as its linear part.
The nonlinear source retains the whole weighted actual history. -/
theorem newton_row_succ (n : Nat) (p : Int) : newtonRow (n+1) p=
    newtonRow n (p-1)+newtonRow n (p+1)+newtonSource n p := by
  unfold newtonRow newtonSource
  rw [transform_succ]
  have he : (fun t => field (t+1) p)=
      (fun t => field t (p-1))+(fun t => field t p)+(fun t => field t (p+1))+
        (fun t => field t p*field t (p+1)) := by
    funext t
    exact field_succ t p
  rw [he]
  simp only [transform_add]
  have hx := double_zero (transform (fun t => field t p) n)
  calc
    _ = (transform (fun t => field t p) n+transform (fun t => field t p) n)+
        (transform (fun t => field t (p-1)) n+transform (fun t => field t (p+1)) n+
          transform (fun t => field t p*field t (p+1)) n) := by ring
    _ = _ := by rw [hx,zero_add]

end NewtonHankel
