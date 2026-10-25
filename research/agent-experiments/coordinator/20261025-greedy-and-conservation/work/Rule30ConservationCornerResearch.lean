module
public import Ruliology.CellularAutomata.Rule30Prize

/-! Uniform finite-word ingredients for conserved local scores of four Rule30
steps. No finite-window census or optimization solver is a premise. -/
@[expose] public section
namespace Rule30ConservationCornerResearch
open Ruliology.CellularAutomata

def shrink : List Bool → List Bool
  | a::b::c::xs => Rule30Jen.rule a b c :: shrink (b::c::xs)
  | _ => []

def four (xs : List Bool) : List Bool := shrink (shrink (shrink (shrink xs)))

def q9 (a b c d e f g h i : Bool) : Bool :=
  (four [a,b,c,d,e,f,g,h,i]).headD false

def q (a : Bool) (xs : List Bool) : Bool :=
  q9 a (xs.getD 0 false) (xs.getD 1 false) (xs.getD 2 false) (xs.getD 3 false)
    (xs.getD 4 false) (xs.getD 5 false) (xs.getD 6 false) (xs.getD 7 false)

theorem q9_left : ∀ a b c d e f g h i : Bool,
    q9 a b c d e f g h i = xor a (q9 false b c d e f g h i) := by decide +kernel

theorem q_left (a : Bool) (xs : List Bool) : q a xs=xor a (q false xs) :=
  q9_left a _ _ _ _ _ _ _ _

theorem q9_right_zero : ∀ a b : Bool,
    q9 a false false false false false false false b=xor a b := by decide +kernel

theorem getD_append_prefix (xs ys : List Bool) (i : Nat) (hi : i<xs.length) :
    (xs++ys).getD i false=xs.getD i false := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem q_append (a b : Bool) (xs : List Bool) (hx : 8≤xs.length) :
    q a (xs++[b])=q a xs := by
  unfold q
  congr 1 <;> apply getD_append_prefix <;> omega

def image : List Bool → List Bool
  | [] => []
  | a::xs => if 8≤xs.length then q a xs :: image xs else []

def preimage : List Bool → List Bool
  | [] => List.replicate 8 false
  | b::xs => let tail:=preimage xs; xor b (q false tail) :: tail

theorem preimage_length (xs : List Bool) : (preimage xs).length=xs.length+8 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [preimage,ih]

/-- Constructive arbitrary-length preimages with eight trailing white cells. -/
theorem image_preimage (xs : List Bool) : image (preimage xs)=xs := by
  induction xs with
  | nil => decide +kernel
  | cons b xs ih =>
    have hp : 8≤(preimage xs).length := by rw [preimage_length]; omega
    have hq : q (xor b (q false (preimage xs))) (preimage xs)=b := by
      rw [q_left]
      cases b <;> cases q false (preimage xs) <;> rfl
    simp only [preimage,image,ite_eq_left hp,hq,ih]

theorem preimage_suffix (xs : List Bool) :
    ∃ u, preimage xs=u++List.replicate 8 false := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons b xs ih =>
    obtain ⟨u,hu⟩ := ih
    exact ⟨xor b (q false (preimage xs))::u,by simp only [preimage,hu,List.cons_append]⟩

theorem image_white_suffix (u : List Bool) (b : Bool) :
    image (u++List.replicate 8 false++[b])=
      image (u++List.replicate 8 false)++[b] := by
  induction u with
  | nil => cases b <;> decide +kernel
  | cons a u ih =>
    have hx : 8≤(u++List.replicate 8 false).length := by simp
    have hy : 8≤((u++List.replicate 8 false)++[b]).length := by simp
    simp only [List.cons_append,image,ite_eq_left hx,ite_eq_left hy,q_append a b _ hx,ih]

/-- Two freely chosen outer input cells vary only the two endpoint outputs;
the desired interior is arbitrary and has unbounded length. -/
theorem image_rectangle (a b : Bool) (ys : List Bool) :
    image (a::(preimage ys++[b]))=
      xor a (q false (preimage ys)) :: (ys++[b]) := by
  obtain ⟨u,hu⟩ := preimage_suffix ys
  have hs := image_white_suffix (a::u) b
  simp only [List.cons_append,←hu] at hs
  rw [hs]
  have hp : 8≤(preimage ys).length := by rw [preimage_length]; omega
  simp only [image,ite_eq_left hp,image_preimage,List.cons_append]
  exact congrArg (fun z => z::(ys++[b])) (q_left a (preimage ys))

/-- Local conservation with a potential on the maximal proper input window.
Input length m+8 represents the exact four-step radius-four light cone.
The old density's window omits the two outer input cells. -/
def Conserved (m : Nat) (h p : List Bool → Int) : Prop :=
  ∀ mid : List Bool, mid.length=m+6 → ∀ a b : Bool,
    h (image (a::(mid++[b])))=
      h ((mid.drop 3).take m)+p (a::mid)-p (mid++[b])

/-- Every conserved density at ANY window length >=2 has zero endpoint
mixed difference. This is the uniform range-reduction obstruction. -/
theorem conserved_rectangle (ys : List Bool) (h p : List Bool → Int)
    (hc : Conserved (ys.length+2) h p) :
    h (false::(ys++[false]))+h (true::(ys++[true]))=
      h (false::(ys++[true]))+h (true::(ys++[false])) := by
  have hl : (preimage ys).length=ys.length+2+6 := by rw [preimage_length]
  have h00 := hc (preimage ys) hl false false
  have h01 := hc (preimage ys) hl false true
  have h10 := hc (preimage ys) hl true false
  have h11 := hc (preimage ys) hl true true
  rw [image_rectangle] at h00 h01 h10 h11
  cases hh : q false (preimage ys) <;> simp only [hh] at h00 h01 h10 h11 <;>
    change _ at h00 h01 h10 h11 <;> simp only [Bool.false_xor,Bool.true_xor,
      Bool.not_false,Bool.not_true] at h00 h01 h10 h11 <;> omega

def potential (h : List Bool → Int) (u : List Bool) : Int := h (false::u)

def shorter (h : List Bool → Int) (u : List Bool) : Int :=
  h (u++[false])-h (false::(u.tail++[false]))+h (false::u)

/-- Explicit cohomology to a shorter local density. No positivity assumption
on the score or on the potential is used. -/
theorem shorten_density (ys : List Bool) (h p : List Bool → Int)
    (hc : Conserved (ys.length+2) h p) (a b : Bool) :
    h (a::(ys++[b]))=shorter h (a::ys)+
      potential h (ys++[b])-potential h (a::ys) := by
  have hr := conserved_rectangle ys h p hc
  unfold shorter potential
  simp only [List.cons_append,List.tail_cons]
  cases a <;> cases b <;> omega

end Rule30ConservationCornerResearch
