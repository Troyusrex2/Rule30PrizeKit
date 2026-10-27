module
public import Rule30CASymbolic

/-! The symbolic invariant and coordinate-stream identity for the literal
finite CA action. Arbitrary remaining tail bits are allowed. -/
@[expose] public section
namespace Rule30CAInvariantResearch
open Rule30CAObserverResearch Rule30ReaderCanonicalResearch Rule30CASymbolic
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def initial (xs : List Bool) : Row := fun j => xs.getD j false
def invariant (xs : List Bool) : Bool := inv (initial xs)
def coordinate (xs : List Bool) (t j : Nat) : Bool := (titer xs t).getD j false
def stream (xs : List Bool) : Bool := samples (coordinate xs)

theorem take_T (x : Row) (n : Nat) : T (takeBits x n)=takeBits (rstep x) n := by
  simp only [T,C,A,singleStep,take_change,rstep]

theorem take_rit (xs : List Bool) (t : Nat) :
    takeBits (rit (initial xs) t) xs.length=titer xs t := by
  induction t with
  | zero => exact take_initial xs
  | succ t ih => rw [rit,←take_T,ih]; rfl

theorem getD_take (x : Row) (n j : Nat) (hj : j<n) : (takeBits x n).getD j false=x j := by
  induction n generalizing x j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih (fun k => x (k+1)) j (by omega)

theorem coordinate_eq (xs : List Bool) (t j : Nat) (hj : j<xs.length) :
    coordinate xs t j=rit (initial xs) t j := by
  unfold coordinate
  rw [←take_rit]
  exact getD_take _ _ _ hj

theorem initial_T (xs : List Bool) (j : Nat) (hj : j<xs.length) :
    initial (T xs) j=rstep (initial xs) j := coordinate_eq xs 1 j hj

theorem invariant_T (xs : List Bool) (hlen : 6≤xs.length) : invariant (T xs)=invariant xs := by
  unfold invariant
  calc
    inv (initial (T xs))=inv (rstep (initial xs)) :=
      inv_congr (fun j hj => initial_T xs j (by omega))
    _ = inv (initial xs) := invariant_macro _

theorem invariant_titer (xs : List Bool) (hlen : 6≤xs.length) (t : Nat) :
    invariant (titer xs t)=invariant xs := by
  induction t with
  | zero => rfl
  | succ t ih => rw [titer,invariant_T _ (by rw [titer_length]; exact hlen),ih]

theorem samples_congr {R S : Nat → Row} (h : ∀ t j, j<8 → R t j=S t j) :
    samples R=samples S := by
  simp only [samples,terms,List.foldr,h 1 0 (by omega),h 0 1 (by omega),h 0 3 (by omega),
    h 1 3 (by omega),h 2 4 (by omega),h 5 4 (by omega),h 3 5 (by omega),h 5 5 (by omega),
    h 1 6 (by omega),h 2 6 (by omega),h 5 6 (by omega),h 6 6 (by omega),
    h 0 7 (by omega),h 2 7 (by omega),h 16 7 (by omega),h 18 7 (by omega)]

theorem invariant_coordinate_stream (xs : List Bool) (hlen : 8≤xs.length) :
    invariant xs=stream xs := by
  unfold invariant stream
  rw [coordinate_stream_identity]
  exact samples_congr (fun t j hj => (coordinate_eq xs t j (by omega)).symm)

theorem first_T (xs : List Bool) (hlen : 0<xs.length) :
    initial (T xs) 0=!(initial xs 0) := by
  rw [initial_T xs 0 hlen,macro_eight _ 0 (by omega)]
  rfl

theorem third_T (xs : List Bool) (hlen : 3≤xs.length) :
    initial (T xs) 2=initial xs 2 := by
  rw [initial_T xs 2 (by omega),macro_eight _ 2 (by omega)]
  rfl

theorem titer_step (xs : List Bool) (t : Nat) : titer (T xs) t=titer xs (t+1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [titer,ih]

end Rule30CAInvariantResearch
