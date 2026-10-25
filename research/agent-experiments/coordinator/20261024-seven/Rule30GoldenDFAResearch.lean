import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-! A bit-parallel automaton for no 00 and no 11111. These generic lemmas
alone prove no assertion about an even-coordinate decoder or a prize problem. -/

namespace Rule30GoldenDFAResearch

def Golden (s : Nat → Bool) : Prop :=
  (∀ k, s k = false → s (k+1) = true) ∧
  (∀ k, ¬(s k = true ∧ s (k+1) = true ∧ s (k+2) = true ∧
    s (k+3) = true ∧ s (k+4) = true))

def next : Nat → Bool → Nat
  | 0,false => 6 | 0,true => 1
  | 1,false => 0 | 1,true => 2
  | 2,false => 0 | 2,true => 3
  | 3,false => 0 | 3,true => 4
  | 4,false => 0 | 4,true => 6
  | 5,false => 0 | 5,true => 1
  | _,_ => 6

def choice (s : Nat → Bool) (d : Nat) : Nat :=
  if d = 0 then 5 else if s (d-1) = false then 0 else
  if d = 1 ∨ s (d-2) = false then 1 else
  if d = 2 ∨ s (d-3) = false then 2 else
  if d = 3 ∨ s (d-4) = false then 3 else 4

theorem choice_lt (s : Nat → Bool) (d : Nat) : choice s d < 6 := by
  unfold choice
  split <;> first | decide | skip
  split <;> first | decide | skip
  split <;> first | decide | skip
  split <;> first | decide | skip
  split <;> decide

theorem choice_next {s : Nat → Bool} (h : Golden s) (d : Nat) :
    next (choice s d) (s d) = choice s (d+1) := by
  rcases (show d=0 ∨ d=1 ∨ d=2 ∨ d=3 ∨ 4≤d by omega) with rfl | rfl | rfl | rfl | hd
  · cases h0 : s 0 <;> simp [choice,next,h0]
  · have hh := h.1 0
    cases h0 : s 0 <;> cases h1 : s 1 <;> simp_all [choice,next]
  · have hh := h.1 1
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> simp_all [choice,next]
  · have hh := h.1 2
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3 <;>
      simp_all [choice,next]
  · have hp := h.1 (d-1)
    have hf := h.2 (d-4)
    have ha : d ≠ 0 := by omega
    have hb : d ≠ 1 := by omega
    have hc : d ≠ 2 := by omega
    have he : d ≠ 3 := by omega
    have hA : d+1 ≠ 0 := by omega
    have hB : d+1 ≠ 1 := by omega
    have hC : d+1 ≠ 2 := by omega
    have hD : d+1 ≠ 3 := by omega
    have hi1 : d+1-1 = d := by omega
    have hi2 : d+1-2 = d-1 := by omega
    have hi3 : d+1-3 = d-2 := by omega
    have hi4 : d+1-4 = d-3 := by omega
    have hj1 : d-4+1 = d-3 := by omega
    have hj2 : d-4+2 = d-2 := by omega
    have hj3 : d-4+3 = d-1 := by omega
    have hj4 : d-4+4 = d := by omega
    have hk : d-1+1 = d := by omega
    cases h0 : s d <;> cases h1 : s (d-1) <;> cases h2 : s (d-2) <;>
      cases h3 : s (d-3) <;> cases h4 : s (d-4) <;> simp_all [choice,next]

def run (s : Nat → Bool) : Nat → Nat
  | 0 => 5
  | d+1 => next (run s d) (s d)

theorem run_eq_choice {s : Nat → Bool} (h : Golden s) (d : Nat) : run s d = choice s d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [run,ih,choice_next h d]

theorem run_lt {s : Nat → Bool} (h : Golden s) (d : Nat) : run s d < 6 := by
  rw [run_eq_choice h d]
  exact choice_lt s d

structure Flags where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  c5 : Nat
deriving DecidableEq

def Flags.at (g : Flags) : Nat → Nat
  | 0 => g.c0 | 1 => g.c1 | 2 => g.c2 | 3 => g.c3 | 4 => g.c4 | 5 => g.c5 | _ => 0

def initial (ALL : Nat) : Flags := ⟨0,0,0,0,0,ALL⟩

def advance (ALL Y : Nat) (g : Flags) : Flags :=
  ⟨(ALL ^^^ Y) &&& (g.c1 ||| g.c2 ||| g.c3 ||| g.c4 ||| g.c5),
   Y &&& (g.c0 ||| g.c5), Y &&& g.c1, Y &&& g.c2, Y &&& g.c3, 0⟩

def empty (g : Flags) : Bool := (g.c0 ||| g.c1 ||| g.c2 ||| g.c3 ||| g.c4 ||| g.c5) == 0

theorem initial_contains {ALL p : Nat} (hALL : ALL.testBit p = true) :
    ((initial ALL).at 5).testBit p = true := hALL

theorem advance_contains {ALL Y p r : Nat} {x : Bool} {g : Flags}
    (hALL : ALL.testBit p = true) (hY : Y.testBit p = x) (hr : r < 6)
    (hg : (g.at r).testBit p = true) (hn : next r x < 6) :
    ((advance ALL Y g).at (next r x)).testBit p = true := by
  rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases x <;> simp_all [next,Flags.at,advance,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor]

theorem not_empty_of_contains {g : Flags} {p r : Nat} (hr : r < 6)
    (hg : (g.at r).testBit p = true) : empty g ≠ true := by
  intro he
  have hz : g.c0 ||| g.c1 ||| g.c2 ||| g.c3 ||| g.c4 ||| g.c5 = 0 := Nat.beq_eq.mp he
  have hb := congrArg (fun a : Nat => a.testBit p) hz
  simp only [Nat.testBit_or,Nat.zero_testBit] at hb
  rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Flags.at]

end Rule30GoldenDFAResearch
