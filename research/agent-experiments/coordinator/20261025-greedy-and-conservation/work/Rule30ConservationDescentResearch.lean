module
public import Rule30ConservationWordResearch

/-! Preserve the conservation equation while shortening its density. The
potential is compressed by proving independence of its final input bit. -/
@[expose] public section
namespace Rule30ConservationDescentResearch
open Rule30ConservationCornerResearch Rule30ConservationWordResearch

theorem crop_length (m : Nat) (xs : List Bool) (hx : m+4≤xs.length) :
    (crop m xs).length=m := by
  simp only [crop,List.length_take,List.length_drop]
  omega

theorem tail_take_succ (m : Nat) (xs : List Bool) :
    (xs.take (m+1)).tail=xs.tail.take m := by cases xs <;> simp

theorem crop_tail (m : Nat) (xs : List Bool) :
    (crop (m+1) xs).tail=crop m xs.tail := by
  unfold crop
  rw [tail_take_succ,List.tail_drop,List.drop_tail]

theorem crop_dropLast (m : Nat) (xs : List Bool) (hx : m+5≤xs.length) :
    (crop (m+1) xs).dropLast=crop m xs := by
  unfold crop
  have hi : m<(xs.drop 4).length := by simp only [List.length_drop]; omega
  rw [List.take_succ_eq_append_getElem hi,List.dropLast_concat]

theorem crop_append (m : Nat) (xs : List Bool) (hx : xs.length=m+8) (b : Bool) :
    crop m (xs++[b])=crop m xs := by
  unfold crop
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem conserved_of_word (m : Nat) (h p : List Bool → Int)
    (hc : ∀ xs, xs.length=m+8 →
      h (image xs)=h (crop m xs)+p xs.dropLast-p xs.tail) : Conserved m h p := by
  intro mid hm a b
  have hx : (a::(mid++[b])).length=m+8 := by simp [hm,Nat.add_assoc]
  have hh:=hc (a::(mid++[b])) hx
  have hp : (a::(mid++[b])).dropLast=a::mid := by
    change ((a::mid)++[b]).dropLast=a::mid
    exact List.dropLast_concat
  simpa only [crop_outer m mid hm a b,hp,List.tail_cons] using hh

theorem shorten_word (m : Nat) (hm : 1≤m) (h p : List Bool → Int)
    (hc : Conserved (m+1) h p) (xs : List Bool) (hx : xs.length=m+1) :
    h xs=shorter h xs.dropLast+potential h xs.tail-potential h xs.dropLast := by
  cases xs with
  | nil => simp at hx
  | cons a xs =>
    have hn : xs≠[] := by intro he; simp [he] at hx; omega
    let b:=xs.getLast hn
    let ys:=xs.dropLast
    have he : ys++[b]=xs := List.dropLast_concat_getLast hn
    have hl : ys.length+2=m+1 := by simp only [ys,List.length_dropLast,List.length_cons] at *; omega
    have hc' : Conserved (ys.length+2) h p := by rw [hl]; exact hc
    have hh:=shorten_density ys h p hc' a b
    simpa only [List.dropLast_concat,List.tail_cons,List.dropLast_cons_of_ne_nil hn,ys,he] using hh

def transport (m : Nat) (h p : List Bool → Int) (xs : List Bool) : Int :=
  p xs+potential h (image xs)-potential h (crop m xs)

theorem transport_identity (m : Nat) (hm : 1≤m) (h p : List Bool → Int)
    (hc : Conserved (m+1) h p) (xs : List Bool) (hx : xs.length=m+8) (b : Bool) :
    shorter h (image xs)=shorter h (crop m xs)+
      transport m h p xs-transport m h p (xs.tail++[b]) := by
  let w:=xs++[b]
  have hw : w.length=(m+1)+8 := by simp [w,hx,Nat.add_assoc]
  have hn : xs≠[] := by intro he; simp [he] at hx
  have ht : w.tail=xs.tail++[b] := by cases xs <;> simp_all [w]
  have old:=conserved_word (m+1) h p hc w hw
  have hi:=shorten_word m hm h p hc (image w) (by rw [image_length,hw]; omega)
  have hcword:=shorten_word m hm h p hc (crop (m+1) w) (crop_length _ _ (by omega))
  rw [hi,hcword] at old
  have ip : (image w).dropLast=image xs := image_append_dropLast xs b
  have it : (image w).tail=image (xs.tail++[b]) := by rw [image_tail,ht]
  have cp : (crop (m+1) w).dropLast=crop m xs := by
    rw [crop_dropLast m w (by omega),crop_append m xs hx b]
  have ct : (crop (m+1) w).tail=crop m (xs.tail++[b]) := by rw [crop_tail,ht]
  have wp : w.dropLast=xs := List.dropLast_concat
  rw [ip,it,cp,ct,wp,ht] at old
  unfold transport
  omega

theorem transport_last_independent (m : Nat) (hm : 1≤m) (h p : List Bool → Int)
    (hc : Conserved (m+1) h p) (xs : List Bool) (hx : xs.length=m+7) :
    transport m h p (xs++[false])=transport m h p (xs++[true]) := by
  have hl : (false::xs).length=m+8 := by simp [hx,Nat.add_assoc]
  have h0:=transport_identity m hm h p hc (false::xs) hl false
  have h1:=transport_identity m hm h p hc (false::xs) hl true
  simp only [List.tail_cons] at h0 h1
  omega

def reducedPotential (m : Nat) (h p : List Bool → Int) (xs : List Bool) : Int :=
  transport m h p (xs++[false])

theorem transport_reduced (m : Nat) (hm : 1≤m) (h p : List Bool → Int)
    (hc : Conserved (m+1) h p) (xs : List Bool) (hx : xs.length=m+8) :
    transport m h p xs=reducedPotential m h p xs.dropLast := by
  have hn : xs≠[] := by intro he; simp [he] at hx
  let b:=xs.getLast hn
  have he : xs.dropLast++[b]=xs := List.dropLast_concat_getLast hn
  have hl : xs.dropLast.length=m+7 := by rw [List.length_dropLast,hx]; omega
  have hi:=transport_last_independent m hm h p hc xs.dropLast hl
  unfold reducedPotential
  rw [←he]
  simp only [List.dropLast_concat]
  cases hb : b
  · rfl
  · exact hi.symm

/-- The explicit shorter density again has a potential of the proper compact
window length. This is the induction step, uniformly for every m>=1. -/
theorem shorter_conserved (m : Nat) (hm : 1≤m) (h p : List Bool → Int)
    (hc : Conserved (m+1) h p) :
    Conserved m (shorter h) (reducedPotential m h p) := by
  apply conserved_of_word
  intro xs hx
  have hh:=transport_identity m hm h p hc xs hx false
  rw [transport_reduced m hm h p hc xs hx] at hh
  exact hh

end Rule30ConservationDescentResearch
