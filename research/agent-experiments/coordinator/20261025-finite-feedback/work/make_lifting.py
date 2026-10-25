"""Generate the finite transformation-monoid certificate, not proof conclusions."""
from pathlib import Path
from collections import deque
root=Path(__file__).resolve().parent
T=[(0,3,1,3),(1,2,0,2)];seen={(tuple(range(4)),False)};q=deque(seen)
while q:
    f,z=q.popleft()
    for b in range(2):
        k=(tuple(T[b][v] for v in f),z or b==0)
        if k not in seen:seen.add(k);q.append(k)
def literal(z):return ',\n  '.join('('+', '.join(map(str,f))+')' for f,k in sorted(seen) if k==z)
template='''import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! The four-state transfer map of sideways reconstruction. A block containing
a zero has no spatial cycle of odd length three: its fifth and third powers
agree, uniformly in block length. This is not a Rule 30 prize solution. -/
namespace Rule30SpatialLiftingResearch

abbrev State := Fin 4
abbrev Code := State × State × State × State

def step (u : Bool) (s : State) : State :=
  match s.val with
  | 0 => if u then 1 else 0
  | 1 => if u then 2 else 3
  | 2 => if u then 0 else 1
  | _ => if u then 2 else 3

def encode (a b : Bool) : State :=
  if a then (if b then 3 else 2) else (if b then 1 else 0)

theorem step_encode (u a b : Bool) :
    step u (encode a b) = encode b (xor u (b || a)) := by
  cases u <;> cases a <;> cases b <;> rfl

def eval (c : Code) (s : State) : State :=
  match s.val with
  | 0 => c.1
  | 1 => c.2.1
  | 2 => c.2.2.1
  | _ => c.2.2.2

def post (u : Bool) (c : Code) : Code :=
  (step u c.1, step u c.2.1, step u c.2.2.1, step u c.2.2.2)

theorem eval_post (u : Bool) (c : Code) (s : State) :
    eval (post u c) s = step u (eval c s) := by
  obtain ⟨s, hs⟩ := s
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

def oneCodes : List Code := [
  @ONES@
]

def zeroCodes : List Code := [
  @ZEROS@
]

theorem zero_checked : zeroCodes.all (fun c => [false,true].all
    (fun b => zeroCodes.contains (post b c))) = true := by decide

theorem one_true_checked : oneCodes.all
    (fun c => oneCodes.contains (post true c)) = true := by decide

theorem one_false_checked : oneCodes.all
    (fun c => zeroCodes.contains (post false c)) = true := by decide

theorem zero_closed (c : Code) (hc : c ∈ zeroCodes) (b : Bool) :
    post b c ∈ zeroCodes := by
  have h := List.all_eq_true.mp zero_checked c hc
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h b hb)

theorem one_true (c : Code) (hc : c ∈ oneCodes) : post true c ∈ oneCodes :=
  List.contains_iff_mem.mp (List.all_eq_true.mp one_true_checked c hc)

theorem one_false (c : Code) (hc : c ∈ oneCodes) : post false c ∈ zeroCodes :=
  List.contains_iff_mem.mp (List.all_eq_true.mp one_false_checked c hc)

def wordCode : List Bool → Code
  | [] => (0,1,2,3)
  | b::w => post b (wordCode w)

def runWord : List Bool → State → State
  | [], s => s
  | b::w, s => step b (runWord w s)

theorem eval_word (w : List Bool) (s : State) : eval (wordCode w) s = runWord w s := by
  induction w with
  | nil =>
    obtain ⟨s,hs⟩ := s
    have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  | cons b w ih => simpa [wordCode,runWord,eval_post] using congrArg (step b) ih

theorem word_class (w : List Bool) :
    (wordCode w ∈ oneCodes ∧ false ∉ w) ∨
    (wordCode w ∈ zeroCodes ∧ false ∈ w) := by
  induction w with
  | nil => exact Or.inl ⟨by decide, by simp⟩
  | cons b w ih =>
    rcases ih with ⟨hc,hz⟩ | ⟨hc,hz⟩
    · cases b with
      | false => exact Or.inr ⟨one_false _ hc, by simp⟩
      | true => exact Or.inl ⟨one_true _ hc, by simp [hz]⟩
    · exact Or.inr ⟨zero_closed _ hc b, by simp [hz]⟩

def power (f : State → State) : Nat → State → State
  | 0, s => s
  | n+1, s => f (power f n s)

theorem power_checked : zeroCodes.all (fun c => ([0,1,2,3] : List State).all
    (fun s => power (eval c) 5 s == power (eval c) 3 s)) = true := by decide

theorem zero_power (c : Code) (hc : c ∈ zeroCodes) (s : State) :
    power (eval c) 5 s = power (eval c) 3 s := by
  have h := List.all_eq_true.mp power_checked c hc
  have hs : s ∈ ([0,1,2,3] : List State) := by
    obtain ⟨s,hs⟩ := s
    have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> simp
  exact beq_iff_eq.mp (List.all_eq_true.mp h s hs)

/-- Every finite driver block containing a zero settles after three block
applications to a cycle of period dividing two. No bound on block length. -/
theorem word_power (w : List Bool) (hz : false ∈ w) (s : State) :
    power (runWord w) 5 s = power (runWord w) 3 s := by
  have hc : wordCode w ∈ zeroCodes := by
    rcases word_class w with ⟨_,h⟩ | ⟨h,_⟩
    · exact False.elim (h hz)
    · exact h
  have hf : eval (wordCode w) = runWord w := funext (eval_word w)
  simpa [hf] using zero_power _ hc s

theorem word_power_period (w : List Bool) (hz : false ∈ w)
    (k : Nat) (hk : 3 ≤ k) (s : State) :
    power (runWord w) (k+2) s = power (runWord w) k s := by
  obtain ⟨n,rfl⟩ : ∃ n, k=3+n := ⟨k-3,by omega⟩
  clear hk
  induction n with
  | zero => exact word_power w hz s
  | succ n ih => simpa [Nat.add_assoc,power] using congrArg (runWord w) ih

end Rule30SpatialLiftingResearch
'''
source=template.replace('@ONES@',literal(False)).replace('@ZEROS@',literal(True))
(root/'Rule30SpatialLiftingResearch.lean').write_text(source,encoding='utf-8')
print({'codes':len(seen),'one_codes':sum(not z for _,z in seen),'zero_codes':sum(z for _,z in seen)})
