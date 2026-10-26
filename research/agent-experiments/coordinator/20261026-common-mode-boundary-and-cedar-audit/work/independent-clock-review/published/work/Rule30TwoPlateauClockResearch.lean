module
public import Rule30PeriodicOrPairCertificate
public import Rule30PeriodicOrPeriodResearch

/-! An arbitrary-even-clock obstruction to a periodic newest OR, one cell farther back.
The paired six-cell graph has free older inputs. Its two-step invariant
is proved for arbitrary path length and connected to literal Actual strips.
Neither a period for older inputs nor a finite census of clocks is assumed.
This remains a diagonal-clock result, not a solution of Prize Problem 1. -/
@[expose] public section
namespace Rule30TwoPlateauClockResearch
open Rule30CommonPastResearch
open Rule30PeriodicOrPairCertificate
open Rule30PeriodicOrPeriodResearch
open Rule30SaturatedOrPeriodResearch (anti_double)
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

theorem base_mem (q : Nat) (hq : q<4096) (hg : good q=true) : q∈level0 := by
  have h := List.all_eq_true.mp base_check q (List.mem_range.mpr hq)
  rw [hg,Bool.not_true,Bool.false_or,mask0_eq] at h
  exact (bits_mem level0 q).mp h

theorem prune_mem (A B : List Nat) (am bm : Nat)
    (ha : am=bits A) (hb : bm=bits B)
    (hc : A.all (fun q => (List.range 16).all
      (fun u => !(am.testBit (advance q u)) || bm.testBit q))=true)
    (q u : Nat) (hq : q∈A) (hu : u<16) (hn : advance q u∈A) : q∈B := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp hc q hq) u (List.mem_range.mpr hu)
  have hn' : am.testBit (advance q u)=true := by
    rw [ha];exact (bits_mem A _).mpr hn
  rw [hn',Bool.not_true,Bool.false_or,hb] at h
  exact (bits_mem B q).mp h

theorem path_mem (x u : Nat → Nat)
    (hb : ∀ t, x t<4096) (hg : ∀ t, good (x t)=true)
    (hu : ∀ t, u t<16) (hs : ∀ t, x (t+1)=advance (x t) (u t)) :
    ∀ t, x t∈level3 := by
  have h0 : ∀ t, x t∈level0 := fun t => base_mem _ (hb t) (hg t)
  have h1 : ∀ t, x t∈level1 := by
    intro t
    apply prune_mem level0 level1 mask0 mask1 mask0_eq mask1_eq prune0_check _ _ (h0 t) (hu t)
    rw [←hs t];exact h0 (t+1)
  have h2 : ∀ t, x t∈level2 := by
    intro t
    apply prune_mem level1 level2 mask1 mask2 mask1_eq mask2_eq prune1_check _ _ (h1 t) (hu t)
    rw [←hs t];exact h1 (t+1)
  intro t
  apply prune_mem level2 level3 mask2 mask3 mask2_eq mask3_eq prune2_check _ _ (h2 t) (hu t)
  rw [←hs t];exact h2 (t+1)

theorem successor_mem (q u : Nat) (hq : q∈level3) (hu : u<16)
    (hn : advance q u∈level3) : advance q u∈successors q := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp successors_check q hq) u (List.mem_range.mpr hu)
  have hm : mask3.testBit (advance q u)=true := by
    rw [mask3_eq];exact (bits_mem level3 _).mpr hn
  rw [hm,Bool.not_true,Bool.false_or] at h
  exact of_decide_eq_true h

theorem inv_initial (q : Nat) (hq : q∈level3) : Inv (projection q) q=true :=
  List.all_eq_true.mp initial_check q hq

theorem projection_mem (q : Nat) (hq : q∈level3) : projection q∈projections :=
  of_decide_eq_true (List.all_eq_true.mp projection_check q hq)

theorem inv_two_steps (p q r s : Nat) (hp : p∈projections) (hq : q∈level3)
    (hi : Inv p q=true) (hr : r∈successors q) (hs : s∈successors r) : Inv p s=true := by
  have h := List.all_eq_true.mp closed_check p hp
  have hq' := List.all_eq_true.mp h q hq
  rw [hi,Bool.not_true,Bool.false_or] at hq'
  exact List.all_eq_true.mp (List.all_eq_true.mp hq' r hr) s hs

theorem inv_excludes_swap (p q : Nat) (hp : p∈projections) (hq : q∈level3)
    (hi : Inv p q=true) : projection q≠swap p := by
  have h := List.all_eq_true.mp excludes_check p hp
  have hq' := List.all_eq_true.mp h q hq
  rw [hi,Bool.not_true,Bool.false_or] at hq'
  exact of_decide_eq_true hq'

/-- Every even length, with no upper bound on the path length. -/
theorem even_path_no_swap (x : Nat → Nat)
    (hm : ∀ t, x t∈level3) (hs : ∀ t, x (t+1)∈successors (x t)) (N : Nat) :
    projection (x (2*N))≠swap (projection (x 0)) := by
  have hp := projection_mem _ (hm 0)
  have hi : ∀ n, Inv (projection (x 0)) (x (2*n))=true := by
    intro n
    induction n with
    | zero => simpa using inv_initial _ (hm 0)
    | succ n ih =>
      have h := inv_two_steps _ _ _ _ hp (hm (2*n)) ih (hs (2*n)) (hs (2*n+1))
      simpa only [show 2*(n+1)=2*n+1+1 by omega] using h
  exact inv_excludes_swap _ _ hp (hm (2*N)) (hi N)

def rowCode (n m l k h g : Bool) : Nat :=
  n.toNat + 2*m.toNat + 4*l.toNat + 8*k.toNat + 16*h.toNat + 32*g.toNat
def twoCode (n m : Bool) : Nat := n.toNat + 2*m.toNat

theorem rowCode_lt : ∀ n m l k h g : Bool, rowCode n m l k h g<64 := by decide +kernel
theorem twoCode_lt : ∀ n m : Bool, twoCode n m<4 := by decide +kernel
theorem rowStep_code : ∀ n m l k h g n' m' : Bool,
    rowStep (rowCode n m l k h g) (twoCode n' m') =
    rowCode n' m' (xor l (m || n)) (xor k (l || m))
      (xor h (k || l)) (xor g (h || k)) := by decide +kernel

theorem good_pair_code : ∀ n m l k h g n' m' l' k' h' g' : Bool,
    good (rowCode n m l k h g + 64*rowCode n' m' l' k' h' g') =
    (!(xor (g || h) (g' || h')) && xor k k' && !(xor l l')) := by decide +kernel

theorem pair_parts (a b : Nat) (ha : a<64) :
    (a+64*b)%64=a ∧ (a+64*b)/64=b := by omega

theorem advance_pair (a b u v : Nat) (ha : a<64) (hu : u<4) :
    advance (a+64*b) (u+4*v)=rowStep a u+64*rowStep b v := by
  have h := pair_parts a b ha
  have hi : (u+4*v)%4=u ∧ (u+4*v)/4=v := by omega
  simp only [advance,h.1,h.2,hi.1,hi.2]

theorem projection_pair (a b : Nat) (ha : a<64) :
    projection (a+64*b)=a/4+16*(b/4) := by
  have h := pair_parts a b ha
  simp only [projection,h.1,h.2]

theorem swap_pair (a b : Nat) (ha : a<16) : swap (a+16*b)=b+16*a := by
  unfold swap
  have h : (a+16*b)/16=b ∧ (a+16*b)%16=a := by omega
  rw [h.1,h.2]

theorem rowCode_projection : ∀ n m l k h g : Bool,
    rowCode n m l k h g/4=l.toNat+2*k.toNat+4*h.toNat+8*g.toNat := by decide +kernel

def row (a : Nat → Nat → Bool) (j t : Nat) : Nat :=
  rowCode (a t j) (a t (j+1)) (a t (j+2)) (a t (j+3)) (a t (j+4)) (a t (j+5))
def pair (a : Nat → Nat → Bool) (j R t : Nat) : Nat := row a j t+64*row a j (t+R)
def input (a : Nat → Nat → Bool) (j R t : Nat) : Nat :=
  twoCode (a (t+1) j) (a (t+1) (j+1)) +
    4*twoCode (a ((t+R)+1) j) (a ((t+R)+1) (j+1))

theorem row_lt (a : Nat → Nat → Bool) (j t : Nat) : row a j t<64 :=
  rowCode_lt _ _ _ _ _ _
theorem pair_lt (a : Nat → Nat → Bool) (j R t : Nat) : pair a j R t<4096 := by
  have h0 := row_lt a j t
  have h1 := row_lt a j (t+R)
  unfold pair;omega
theorem input_lt (a : Nat → Nat → Bool) (j R t : Nat) : input a j R t<16 := by
  have h0 := twoCode_lt (a (t+1) j) (a (t+1) (j+1))
  have h1 := twoCode_lt (a ((t+R)+1) j) (a ((t+R)+1) (j+1))
  unfold input;omega

theorem row_actual (a : Nat → Nat → Bool) (ha : Actual a) (j t : Nat) :
    row a j (t+1)=rowStep (row a j t) (twoCode (a (t+1) j) (a (t+1) (j+1))) := by
  have h2 : a (t+1) (j+2)=xor (a t (j+2)) (a t (j+1) || a t j) := ha t (j+2)
  have h3 : a (t+1) (j+3)=xor (a t (j+3)) (a t (j+2) || a t (j+1)) := ha t (j+3)
  have h4 : a (t+1) (j+4)=xor (a t (j+4)) (a t (j+3) || a t (j+2)) := ha t (j+4)
  have h5 : a (t+1) (j+5)=xor (a t (j+5)) (a t (j+4) || a t (j+3)) := ha t (j+5)
  unfold row
  rw [h2,h3,h4,h5]
  exact (rowStep_code _ _ _ _ _ _ _ _).symm

theorem pair_actual (a : Nat → Nat → Bool) (ha : Actual a) (j R t : Nat) :
    pair a j R (t+1)=advance (pair a j R t) (input a j R t) := by
  unfold pair input
  rw [advance_pair _ _ _ _ (row_lt a j t) (twoCode_lt _ _)]
  rw [show t+1+R=(t+R)+1 by omega,row_actual a ha j t,row_actual a ha j (t+R)]

theorem pair_good (a : Nat → Nat → Bool) (j R : Nat)
    (hk : ∀ t, a (t+R) (j+3)=xor (a t (j+3)) true)
    (hl : ∀ t, a (t+R) (j+2)=a t (j+2))
    (ho : ∀ t, (a (t+R) (j+5) || a (t+R) (j+4))=(a t (j+5) || a t (j+4))) :
    ∀ t, good (pair a j R t)=true := by
  intro t
  unfold pair row
  rw [good_pair_code,ho t,hk t,hl t]
  have same : ∀ b : Bool, xor b b=false := by decide
  rw [same]
  cases a t (j+3) <;> cases a t (j+2) <;> rfl

theorem pair_endpoint_swap (a : Nat → Nat → Bool) (j R : Nat)
    (hl : ∀ t, a (t+2*R) (j+2)=a t (j+2))
    (hk : ∀ t, a (t+2*R) (j+3)=a t (j+3))
    (hh : ∀ t, a (t+2*R) (j+4)=a t (j+4))
    (hg : ∀ t, a (t+2*R) (j+5)=a t (j+5)) :
    projection (pair a j R R)=swap (projection (pair a j R 0)) := by
  have hp : ∀ t, row a j (t+2*R)/4=row a j t/4 := by
    intro t
    unfold row
    rw [rowCode_projection,rowCode_projection,hl t,hk t,hh t,hg t]
  have he : row a j (R+R)/4=row a j 0/4 := by
    simpa only [Nat.zero_add,show R+R=2*R by omega] using hp 0
  unfold pair
  rw [projection_pair _ _ (row_lt a j R),projection_pair _ _ (row_lt a j 0)]
  rw [Nat.zero_add,swap_pair _ _ (by have h := row_lt a j 0;omega),he]

/-- The newest OR cannot discard an even source half-clock across two cells.
There is no assumption that unspecified older profiles share that clock. -/
theorem actual_even_two_plateau_or_clock_rigidity
    (a : Nat → Nat → Bool) (ha : Actual a) (j n : Nat)
    (hk : ∀ t, a (t+2*n) (j+3)=xor (a t (j+3)) true)
    (hl : ∀ t, a (t+2*n) (j+2)=a t (j+2)) :
    ¬(∀ t, (a (t+2*n) (j+5) || a (t+2*n) (j+4))=(a t (j+5) || a t (j+4))) := by
  intro ho
  have newer := actual_periodic_or_double_period a ha j (2*n) hk hl ho
  have kp := anti_double (fun t => a t (j+3)) (2*n) hk
  have lp : ∀ t, a (t+2*(2*n)) (j+2)=a t (j+2) := by
    intro t
    rw [show t+2*(2*n)=(t+2*n)+2*n by omega,hl (t+2*n),hl t]
  let x := pair a j (2*n)
  let u := input a j (2*n)
  have mem : ∀ t, x t∈level3 := path_mem x u (pair_lt a j (2*n))
    (pair_good a j (2*n) hk hl ho) (input_lt a j (2*n)) (pair_actual a ha j (2*n))
  have hs : ∀ t, x (t+1)∈successors (x t) := by
    intro t
    have he := pair_actual a ha j (2*n) t
    change x (t+1)=advance (x t) (u t) at he
    rw [he]
    apply successor_mem _ _ (mem t) (input_lt a j (2*n) t)
    rw [←he];exact mem (t+1)
  exact even_path_no_swap x mem hs n
    (pair_endpoint_swap a j (2*n) lp kp newer.1 newer.2)

/-- Integrating the newer OR cannot restore the lost half-clock. -/
theorem actual_third_column_no_half_period
    (a : Nat → Nat → Bool) (ha : Actual a) (j n : Nat)
    (hk : ∀ t, a (t+2*n) (j+3)=xor (a t (j+3)) true)
    (hl : ∀ t, a (t+2*n) (j+2)=a t (j+2)) :
    ¬(∀ t, a (t+2*n) (j+6)=a t (j+6)) := by
  intro hx
  apply actual_even_two_plateau_or_clock_rigidity a ha j n hk hl
  intro t
  have h0 : a (t+1) (j+6)=xor (a t (j+6)) (a t (j+5) || a t (j+4)) := ha t (j+6)
  have h1 : a ((t+2*n)+1) (j+6)=xor (a (t+2*n) (j+6))
      (a (t+2*n) (j+5) || a (t+2*n) (j+4)) := ha (t+2*n) (j+6)
  rw [show (t+2*n)+1=(t+1)+2*n by omega,hx (t+1),hx t,h0] at h1
  have cancel : ∀ b x y : Bool, xor b x=xor b y → y=x := by decide
  exact cancel _ _ _ h1

/-- The same exclusion survives an arbitrary finite transient. -/
theorem actual_third_column_no_eventual_half_period
    (a : Nat → Nat → Bool) (ha : Actual a) (j n T : Nat)
    (hk : ∀ t, a (t+2*n) (j+3)=xor (a t (j+3)) true)
    (hl : ∀ t, a (t+2*n) (j+2)=a t (j+2)) :
    ¬(∀ t, T≤t → a (t+2*n) (j+6)=a t (j+6)) := by
  intro hx
  let b := fun t i => a (t+T) i
  have hb : Actual b := by
    intro t i
    change a ((t+1)+T) i=march (a (t+T)) i
    simpa only [show (t+1)+T=(t+T)+1 by omega] using ha (t+T) i
  have bk : ∀ t, b (t+2*n) (j+3)=xor (b t (j+3)) true := by
    intro t
    change a ((t+2*n)+T) (j+3)=xor (a (t+T) (j+3)) true
    simpa only [show (t+2*n)+T=(t+T)+2*n by omega] using hk (t+T)
  have bl : ∀ t, b (t+2*n) (j+2)=b t (j+2) := by
    intro t
    change a ((t+2*n)+T) (j+2)=a (t+T) (j+2)
    simpa only [show (t+2*n)+T=(t+T)+2*n by omega] using hl (t+T)
  apply actual_third_column_no_half_period b hb j n bk bl
  intro t
  change a ((t+2*n)+T) (j+6)=a (t+T) (j+6)
  simpa only [show (t+2*n)+T=(t+T)+2*n by omega] using hx (t+T) (by omega)

end Rule30TwoPlateauClockResearch
