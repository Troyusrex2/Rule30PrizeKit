module
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! A fast inverse discrepancy on the six-tick periodic completion at the
fixed white wall. Rows may have infinite support. The statements concern
predecessors of a periodic completion. -/
@[expose] public section
namespace ReverseFront
open Ruliology.CellularAutomata.Rule30Jen

abbrev Row := Nat → Bool
def Step (z x : Row) : Prop :=
  rule (z 1) (z 0) false = x 0 ∧
  ∀ i, rule (z (i+2)) (z (i+1)) (z i) = x (i+1)

/-- Our bit j lives at depth j+1 in the kit. Depth zero is the white wall. -/
def kitSeed (x : Row) : Row
  | 0 => false
  | j+1 => x j

open Ruliology.CellularAutomata.Rule30ZeroBoundary in
theorem step_iff_zrow (z x : Row) :
    Step z x ↔ ∀ j, zrow (kitSeed z) 1 (j+1) = x j := by
  constructor
  · intro hs j
    cases j with
    | zero => exact hs.1
    | succ i => exact hs.2 i
  · intro hs
    exact ⟨hs 0, fun i => hs (i+1)⟩

def e (i : Nat) : Bool := (2457691783802708131298419 : Nat).testBit (i%84)

-- The exact six-tick reference, indexed by time running backwards.
def base (h : Nat) : Row
  | 0 => decide (h%6 ≠ 0)
  | i+1 => e (i+1+19+70*h)

def mask : Nat → Nat
  | 6 => 3 | 7 => 54 | 8 => 20 | 9 => 40 | 10 => 64371
  | 11 => 1055766230 | 12 => 316298327 | 13 => 3697027230
  | 14 => 1735782500 | 15 => 966107336 | 16 => 240235658035
  | _ => 0

def sample (h j : Nat) : Bool :=
  xor (base h j) (if j<38 then (mask h).testBit j else false)

def clamp (i : Nat) : Nat := if i<38 then i else 38+(i-38)%84
theorem clamp_lt (i : Nat) : clamp i<122 := by unfold clamp; split <;> omega

theorem sample_clamp (h i k : Nat) : sample h (clamp i+k)=sample h (i+k) := by
  unfold clamp
  split
  · rfl
  · rename_i hi
    have ha : 38+(i-38)%84+k ≥ 38 := by omega
    have hb : i+k ≥ 38 := by omega
    unfold sample
    simp only [ite_eq_right (by omega : ¬38+(i-38)%84+k<38),ite_eq_right (by omega : ¬i+k<38),Bool.xor_false]
    have hx : ∀ j, 0<j → base h j=e (j+19+70*h) := by intro j hj; cases j <;> simp_all [base]
    rw [hx _ (by omega),hx _ (by omega)]
    unfold e
    congr 1
    omega

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sample_steps (h : Nat) (hh : h<16) : Step (sample (h+1)) (sample h) := by
  have table : ∀ a : Fin 16,
      rule (sample (a.val+1) 1) (sample (a.val+1) 0) false = sample a.val 0 ∧
      ∀ q : Fin 122, rule (sample (a.val+1) (q.val+2)) (sample (a.val+1) (q.val+1))
        (sample (a.val+1) q.val) = sample a.val (q.val+1) := by decide +kernel
  refine ⟨(table ⟨h,hh⟩).1,?_⟩
  intro i
  have eqn := (table ⟨h,hh⟩).2 ⟨clamp i,clamp_lt i⟩
  change rule (sample (h+1) (clamp i+2)) (sample (h+1) (clamp i+1))
    (sample (h+1) (clamp i+0)) = sample h (clamp i+1) at eqn
  have last : sample (h+1) (clamp i)=sample (h+1) i := sample_clamp _ _ 0
  simpa only [sample_clamp,Nat.add_zero,last] using eqn

theorem legal_entry :
    (∀ h : Fin 17, sample h.val 0 = decide (h.val≠0 ∧ h.val≠10 ∧ h.val≠16)) ∧
    (∀ j, sample 0 j=base 0 j) := by
  constructor
  · decide +kernel
  · intro j; simp [sample,mask]

theorem e_shift (j k : Nat) : e (j+84*k)=e j := by simp [e]

theorem base_time (h n j : Nat) : base (h+6*n) j=base h j := by
  cases j with
  | zero => simp [base,Nat.add_mod]
  | succ j =>
    change e (j+1+19+70*(h+6*n))=e (j+1+19+70*h)
    rw [show j+1+19+70*(h+6*n)=j+1+19+70*h+84*(5*n) by omega,e_shift]

theorem base_clamp (h i k : Nat) : base h (clamp i+k)=base h (i+k) := by
  unfold clamp
  split
  · rfl
  · rename_i hi
    have pos (j : Nat) (hj : 0<j) : base h j=e (j+19+70*h) := by cases j <;> simp_all [base]
    rw [pos _ (by omega),pos _ (by omega)]
    unfold e
    exact congrArg (Nat.testBit _) (by omega)

set_option maxRecDepth 12000 in
theorem base_steps (h : Nat) : Step (base (h+1)) (base h) := by
  have tab : ∀ a : Fin 6,
      rule (base (a.val+1) 1) (base (a.val+1) 0) false = base a.val 0 ∧
      ∀ q : Fin 122, rule (base (a.val+1) (q.val+2)) (base (a.val+1) (q.val+1))
        (base (a.val+1) q.val)=base a.val (q.val+1) := by decide +kernel
  have wrap (j : Nat) : base (h%6) j=base h j := by
    calc base (h%6) j = base (h%6+6*(h/6)) j := (base_time _ _ _).symm
         _ = _ := by rw [Nat.mod_add_div]
  have wrap1 (j : Nat) : base (h%6+1) j=base (h+1) j := by
    calc base (h%6+1) j = base (h%6+1+6*(h/6)) j := (base_time _ _ _).symm
         _ = _ := by rw [show h%6+1+6*(h/6)=h+1 by omega]
  refine ⟨by simpa only [wrap1,wrap] using (tab ⟨h%6,by omega⟩).1,?_⟩
  intro i
  have eqn := (tab ⟨h%6,by omega⟩).2 ⟨clamp i,clamp_lt i⟩
  change rule (base (h%6+1) (clamp i+2)) (base (h%6+1) (clamp i+1))
    (base (h%6+1) (clamp i))=base (h%6) (clamp i+1) at eqn
  have last : base (h+1) (clamp i)=base (h+1) i := base_clamp _ _ 0
  simpa only [wrap1,wrap,base_clamp,last] using eqn

theorem twoSteps {p : Nat → Prop} (zero : p 0) (one : p 1)
    (more : ∀ n, p n → p (n+1) → p (n+2)) (n : Nat) : p n := by
  have pair : ∀ k, p k ∧ p (k+1) := by
    intro k; induction k with
    | zero => exact ⟨zero,one⟩
    | succ k ih => exact ⟨ih.2,more k ih.1 ih.2⟩
  exact (pair n).1

def Front (x : Row) (d : Nat) : Prop :=
  x d = !(e 0) ∧ ∀ k, x (d+1+k)=e (1+k)

def driven : Nat → Bool | 0 => !(e 0) | k+1 => e (k+1)
def readPre (a b : Bool) : Nat → Bool
  | 0 => a | 1 => b
  | k+2 => xor (driven k) (readPre a b (k+1) || readPre a b k)

theorem inv (a b c : Bool) : xor (rule a b c) (b||c)=a := by
  cases a <;> cases b <;> cases c <;> rfl

theorem propagation {x z : Row} {d : Nat} (hd : 0<d) (hx : Front x d)
    (hz : Step z x) : Front z (d+14) := by
  have out : ∀ k, x (d+k)=driven k := by
    intro k; cases k with
    | zero => exact hx.1
    | succ k => simpa [driven, Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx.2 k
  have recu : ∀ k, z (d-1+k)=readPre (z (d-1)) (z d) k := by
    intro k; induction k using twoSteps with
    | zero => rfl
    | one => simp [readPre,show d-1+1=d by omega]
    | more k ih0 ih1 =>
      have law := hz.2 (d-1+k)
      have loc : d-1+k+1=d+k := by omega
      have eqn := inv (z (d-1+k+2)) (z (d-1+k+1)) (z (d-1+k))
      rw [law,loc,out] at eqn
      rw [show d+k=d-1+(k+1) by omega,ih1,ih0] at eqn
      simpa [Nat.add_assoc,readPre] using eqn.symm
  have tab : ∀ a b, readPre a b 15= !(e 0) ∧ readPre a b 16=e 1 ∧ readPre a b 17=e 2 := by decide +kernel
  obtain ⟨ha,hb,hc⟩ := tab (z (d-1)) (z d)
  rw [←recu] at ha hb hc
  refine ⟨by simpa only [show d-1+15=d+14 by omega] using ha,?_⟩
  intro k
  induction k using twoSteps with
  | zero => simpa only [show d-1+16=d+14+1 by omega,Nat.add_zero] using hb
  | one => simpa only [show d-1+17=d+14+1+1 by omega] using hc
  | more k ih0 ih1 =>
    let j := d+14+1+k
    have law := hz.2 j
    have eqn := inv (z (j+2)) (z (j+1)) (z j)
    rw [law] at eqn
    have mid : z (j+1)=e (1+(k+1)) := by
      rw [show j+1=d+14+1+(k+1) by dsimp [j]; omega]
      exact ih1
    have old : z j=e (1+k) := ih0
    have v : x (j+1)=e ((1+k)+15) := by
      simpa [j,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx.2 (15+k)
    rw [mid,old,v] at eqn
    have ether : ∀ r : Fin 84, xor (e (r.val+15)) (e (r.val+1)||e r.val)= e (r.val+2) := by decide +kernel
    have rem (u v : Nat) : e (u%84+v)=e (u+v) := by unfold e; congr 1; omega
    have ee := ether ⟨(1+k)%84,by omega⟩
    change xor (e ((1+k)%84+15)) (e ((1+k)%84+1)||e ((1+k)%84+0))=e ((1+k)%84+2) at ee
    have rem0 : e ((1+k)%84)=e (1+k) := rem (1+k) 0
    simp only [rem,Nat.add_zero,rem0] at ee
    have done : z (j+2)=e ((1+k)+2) := eqn.symm.trans ee
    rw [show d+14+1+(k+2)=j+2 by dsimp [j]; omega, show 1+(k+2)=(1+k)+2 by omega]
    exact done

theorem at_front (n k : Nat) : base (16+n) (37+14*n+k)=e k := by
  have h : 37+14*n+k=(36+14*n+k)+1 := by omega
  rw [h]; change e (36+14*n+k+1+19+70*(16+n))=e k
  rw [show 36+14*n+k+1+19+70*(16+n)=k+84*(14+n) by omega,e_shift]

theorem entry_front : Front (sample 16) 37 := by
  constructor
  · decide +kernel
  · intro k
    unfold sample
    simp only [ite_eq_right (by omega : ¬37+1+k<38),Bool.xor_false]
    rw [show 37+1+k=37+14*0+(1+k) by omega]; exact at_front 0 (1+k)

/-- At time −16 both possible wall bits work. A preceding ten-tick
return and a preceding six-tick return agree through time −15. -/
def alternate (j : Nat) : Bool := if j<2 then !(sample 16 j) else sample 16 j

theorem alternate_entry : Step alternate (sample 15) ∧ alternate 0=true ∧ Front alternate 37 := by
  refine ⟨⟨by decide +kernel, ?_⟩, by decide +kernel, ?_⟩
  · intro i
    by_cases hi : i<2
    · have tab : ∀ q : Fin 2, rule (alternate (q.val+2)) (alternate (q.val+1))
          (alternate q.val)=sample 15 (q.val+1) := by decide +kernel
      exact tab ⟨i,hi⟩
    · simpa only [alternate, ite_eq_right hi, ite_eq_right (by omega : ¬i+1<2),
        ite_eq_right (by omega : ¬i+2<2)] using (sample_steps 15 (by decide)).2 i
  · refine ⟨entry_front.1, fun k => ?_⟩
    simpa only [alternate, ite_eq_right (by omega : ¬37+1+k<2)] using entry_front.2 k

theorem arbitrary_predecessors {rows : Nat → Row} (h0 : rows 0=sample 16)
    (hs : ∀ n, Step (rows (n+1)) (rows n)) (n : Nat) :
    rows n (37+14*n) ≠ base (16+n) (37+14*n) ∧
    ∀ k, rows n (37+14*n+1+k)=base (16+n) (37+14*n+1+k) := by
  have allFront : ∀ m, Front (rows m) (37+14*m) := by
    intro m; induction m with
    | zero => simpa [h0] using entry_front
    | succ m ih =>
      simpa only [show 37+14*(m+1)=37+14*m+14 by omega] using propagation (by omega) ih (hs m)
  obtain ⟨h,hh⟩ := allFront n
  constructor
  · rw [show base (16+n) (37+14*n)=e 0 from at_front n 0,h]
    cases e 0 <;> decide
  · intro k
    rw [show 37+14*n+1+k=37+14*n+(1+k) by omega,at_front]
    simpa only [Nat.add_assoc] using hh k

def predecessor (x : Row) (bit : Bool) : Row
  | 0 => bit
  | 1 => xor (x 0) (bit || false)
  | i+2 => xor (x (i+1)) (predecessor x bit (i+1) || predecessor x bit i)

theorem right_inverse (y b c : Bool) : rule (xor y (b||c)) b c=y := by
  cases y <;> cases b <;> cases c <;> rfl

theorem prescribed_step (x : Row) (bit : Bool) : Step (predecessor x bit) x :=
  ⟨right_inverse _ _ _,fun _ => right_inverse _ _ _⟩

def history (bits : Nat → Bool) : Nat → Row
  | 0 => sample 16
  | n+1 => predecessor (history bits n) (bits n)

/-- Every earlier prescription, including any succession of legal returns,
has a realization with this exact outermost disagreement. -/
theorem prescribed_front (bits : Nat → Bool) (n : Nat) :
    history bits (n+1) 0 = bits n ∧
    history bits n (37+14*n) ≠ base (16+n) (37+14*n) ∧
    ∀ k, history bits n (37+14*n+1+k)=base (16+n) (37+14*n+1+k) :=
  ⟨rfl,arbitrary_predecessors rfl (fun _ => prescribed_step _ _) n⟩

/-- A control with the same ether and another six-periodic near-wall
trace. The six masks list every changed bit in the respective phases. -/
def compactMask : Nat → Nat
  | 0 => 140 | 1 => 239 | 2 => 70 | 3 => 132 | 4 => 107 | _ => 198

def compact (h j : Nat) : Bool :=
  xor (base h j) (if j < 8 then (compactMask (h%6)).testBit j else false)

theorem compact_time (h n j : Nat) : compact (h+6*n) j = compact h j := by
  simp only [compact, base_time, Nat.add_mul_mod_self_left]

theorem compact_tail (h j : Nat) (hj : 8 ≤ j) : compact h j = base h j := by
  simp [compact, show ¬j<8 by omega]

theorem compact_steps (h : Nat) : Step (compact (h+1)) (compact h) := by
  have tab : ∀ a : Fin 6,
      rule (compact (a.val+1) 1) (compact (a.val+1) 0) false = compact a.val 0 ∧
      ∀ i : Fin 8, rule (compact (a.val+1) (i.val+2)) (compact (a.val+1) (i.val+1))
        (compact (a.val+1) i.val)=compact a.val (i.val+1) := by decide +kernel
  have wrap (j : Nat) : compact (h%6) j=compact h j := by
    calc compact (h%6) j = compact (h%6+6*(h/6)) j := (compact_time _ _ _).symm
         _ = _ := by rw [Nat.mod_add_div]
  have wrap1 (j : Nat) : compact (h%6+1) j=compact (h+1) j := by
    calc compact (h%6+1) j = compact (h%6+1+6*(h/6)) j := (compact_time _ _ _).symm
         _ = _ := by rw [show h%6+1+6*(h/6)=h+1 by omega]
  refine ⟨by simpa only [wrap1,wrap] using (tab ⟨h%6,by omega⟩).1,?_⟩
  intro i
  by_cases hi : i<8
  · simpa only [wrap1,wrap] using (tab ⟨h%6,by omega⟩).2 ⟨i,hi⟩
  · simpa only [compact_tail _ _ (by omega : 8 ≤ i+2),
      compact_tail _ _ (by omega : 8 ≤ i+1), compact_tail _ _ (by omega : 8 ≤ i)]
      using (base_steps h).2 i

theorem compact_differs : compact 0 7 ≠ base 0 7 := by decide +kernel

/-- In forward order the near-wall trace is 0,1,0,1,1,0.
The consecutive zeros across the wrap exclude this control from the
six-or-ten return language. -/
theorem compact_trace : ∀ t : Fin 6, compact ((6-t.val)%6) 0 = (26 : Nat).testBit t.val := by
  decide +kernel

/-- Pack a temporal column of period six into the low six bits, in
forward time order. Start from the ordered pair (white wall, trace).
Rule 30 determines the next deeper column by left permutivity. -/
def advance (s : Nat × Nat) : Nat × Nat :=
  let b := s.2
  let nextTime := (b >>> 1) ||| ((b % 2) <<< 5)
  (b, nextTime ^^^ (s.1 ||| b))

theorem advance_local (a b : Fin 64) (t : Fin 6) :
    rule ((advance (a.val,b.val)).2.testBit t.val) (b.val.testBit t.val) (a.val.testBit t.val)
      = b.val.testBit ((t.val+1)%6) := by
  have rot : ∀ (v : Fin 64) (i : Fin 6),
      ((v.val >>> 1) ||| ((v.val%2) <<< 5)).testBit i.val = v.val.testBit ((i.val+1)%6) := by
    decide +kernel
  simp only [advance, Nat.testBit_xor, rot, Nat.testBit_or]
  cases b.val.testBit ((t.val+1)%6) <;> cases b.val.testBit t.val <;> cases a.val.testBit t.val <;> rfl

theorem advance_bound (a b : Fin 64) : (advance (a.val,b.val)).2 < 64 := by
  have rot : ∀ v : Fin 64, ((v.val >>> 1) ||| ((v.val%2) <<< 5)) < 64 := by decide +kernel
  exact Nat.xor_lt_two_pow (n:=6) (rot b) (Nat.or_lt_two_pow (n:=6) a.isLt b.isLt)

def walk : Nat → Nat × Nat → Nat × Nat
  | 0, s => s
  | n+1, s => walk n (advance s)

theorem walk_add (a b : Nat) (s : Nat × Nat) : walk (a+b) s = walk b (walk a s) := by
  induction a generalizing s with
  | zero => simp [walk]
  | succ a ih => rw [Nat.succ_add]; exact ih (advance s)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem six_table : ∀ w : Fin 64,
    walk 93 (0,w.val) = walk 9 (0,w.val) ∧
    (walk 9 (0,w.val) = walk 9 (0,62) ↔ w.val=62 ∨ w.val=26) := by
  decide +kernel

theorem six_returns (w : Fin 64) (k : Nat) :
    walk (9+84*k) (0,w.val) = walk 9 (0,w.val) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 9+84*(k+1)=(9+84*k)+84 by omega, walk_add, ih, ←walk_add]
    exact (six_table w).1

/-- Among ALL six-bit wall words, exactly two ever merge in space with
the in-phase six-tick reference. -/
theorem six_merge_iff (w : Fin 64) :
    (∃ j, walk j (0,w.val) = walk j (0,62)) ↔ w.val=62 ∨ w.val=26 := by
  constructor
  · rintro ⟨j,hj⟩
    apply (six_table w).2.mp
    have more := congrArg (walk (9+84*j-j)) hj
    rw [←walk_add,←walk_add,show j+(9+84*j-j)=9+84*j by omega] at more
    exact (six_returns w j).symm.trans (more.trans (six_returns ⟨62,by decide⟩ j))
  · intro h
    exact ⟨9,(six_table w).2.mpr h⟩

end ReverseFront
