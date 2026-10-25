module
public import Rule30ConservationCornerResearch

/-! Word semantics, compact conservation potentials, and the one-cell base
case for the uniform conservation-law range-reduction argument. -/
@[expose] public section
namespace Rule30ConservationWordResearch
open Rule30ConservationCornerResearch

theorem shrink_length (xs : List Bool) : (shrink xs).length=xs.length-2 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      cases xs with
      | nil => rfl
      | cons c xs =>
        change (shrink (b::c::xs)).length+1=(xs.length+3)-2
        have hh : (shrink (b::c::xs)).length=xs.length := by simpa using ih
        rw [hh]
        omega

theorem four_length (xs : List Bool) : (four xs).length=xs.length-8 := by
  simp only [four,shrink_length]
  omega

theorem four_cons (a : Bool) (xs : List Bool) (hx : 8≤xs.length) :
    four (a::xs)=q a xs::four xs := by
  cases xs with
  | nil => simp at hx
  | cons b xs =>
    cases xs with
    | nil => simp at hx
    | cons c xs =>
      cases xs with
      | nil => simp at hx
      | cons d xs =>
        cases xs with
        | nil => simp at hx
        | cons e xs =>
          cases xs with
          | nil => simp at hx
          | cons f xs =>
            cases xs with
            | nil => simp at hx
            | cons g xs =>
              cases xs with
              | nil => simp at hx
              | cons h xs =>
                cases xs with
                | nil => simp at hx
                | cons i xs => rfl

/-- The sliding nine-cell rule is exactly four physical Rule30 updates
on the whole input word, retaining its complete interior light cone. -/
theorem image_eq_four (xs : List Bool) : image xs=four xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases hx : 8≤xs.length
    · rw [image,ite_eq_left hx,four_cons a xs hx,ih]
    · have he : four (a::xs)=[] := by
        apply List.eq_nil_of_length_eq_zero
        rw [four_length]
        simp only [List.length_cons]
        omega
      simp only [image,ite_eq_right hx,he]

theorem image_length (xs : List Bool) : (image xs).length=xs.length-8 := by
  rw [image_eq_four,four_length]

theorem image_tail (xs : List Bool) : (image xs).tail=image xs.tail := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    by_cases hx : 8≤xs.length
    · simp only [image,ite_eq_left hx,List.tail_cons]
    · have he : image xs=[] := by
        apply List.eq_nil_of_length_eq_zero
        rw [image_length]
        omega
      simp only [image,ite_eq_right hx,List.tail_cons,List.tail_nil,he]

theorem image_append_dropLast (xs : List Bool) (b : Bool) :
    (image (xs++[b])).dropLast=image xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases hx : 8≤xs.length
    · have hy : 8≤(xs++[b]).length := by simp only [List.length_append,List.length_singleton]; omega
      have hn : image (xs++[b])≠[] := by
        intro he
        have hl := image_length (xs++[b])
        rw [he] at hl
        simp only [List.length_nil,List.length_append,List.length_singleton] at hl
        omega
      simp only [List.cons_append,image,ite_eq_left hx,ite_eq_left hy,q_append a b xs hx]
      rw [List.dropLast_cons_of_ne_nil hn,ih]
    · have he : (image ((a::xs)++[b])).dropLast=[] := by
        apply List.eq_nil_of_length_eq_zero
        rw [List.length_dropLast,image_length]
        simp only [List.length_append,List.length_cons,List.length_nil]
        omega
      rw [he]
      simp only [image,ite_eq_right hx]

theorem image_dropLast (xs : List Bool) : image xs.dropLast=(image xs).dropLast := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    have he := List.dropLast_concat_getLast (List.cons_ne_nil a xs)
    have hh := image_append_dropLast (a::xs).dropLast ((a::xs).getLast (List.cons_ne_nil a xs))
    rw [he] at hh
    exact hh.symm

def crop (m : Nat) (xs : List Bool) : List Bool := (xs.drop 4).take m

theorem crop_outer (m : Nat) (mid : List Bool) (hm : mid.length=m+6) (a b : Bool) :
    crop m (a::(mid++[b]))=(mid.drop 3).take m := by
  unfold crop
  rw [List.drop_succ_cons,List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem conserved_word (m : Nat) (h p : List Bool → Int) (hc : Conserved m h p)
    (xs : List Bool) (hx : xs.length=m+8) :
    h (image xs)=h (crop m xs)+p xs.dropLast-p xs.tail := by
  cases xs with
  | nil => simp at hx
  | cons a xs =>
    have hn : xs≠[] := by intro he; simp [he] at hx
    let b:=xs.getLast hn
    let mid:=xs.dropLast
    have he : mid++[b]=xs := List.dropLast_concat_getLast hn
    have hm : mid.length=m+6 := by simp only [mid,List.length_dropLast] at *; simp only [List.length_cons] at hx; omega
    have hh := hc mid hm a b
    rw [←crop_outer m mid hm a b] at hh
    simpa only [List.dropLast_concat,List.tail_cons,List.dropLast_cons_of_ne_nil hn,mid,he] using hh

theorem conserved_one_constant (h p : List Bool → Int) (hc : Conserved 1 h p) :
    h [false]=h [true] := by
  have img : ∀ a b : Bool, image (a::(List.replicate 7 false++[b]))=[xor a b] := by decide +kernel
  have h00:=hc (List.replicate 7 false) (by decide) false false
  have h01:=hc (List.replicate 7 false) (by decide) false true
  have h10:=hc (List.replicate 7 false) (by decide) true false
  have h11:=hc (List.replicate 7 false) (by decide) true true
  rw [img] at h00 h01 h10 h11
  simp only [Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] at h00 h01 h10 h11
  omega

end Rule30ConservationWordResearch
