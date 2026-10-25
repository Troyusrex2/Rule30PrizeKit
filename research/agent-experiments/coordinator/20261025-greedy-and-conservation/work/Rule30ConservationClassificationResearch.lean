module
public import Rule30ConservationCycleResearch

/-! Both directions of the exact all-width integer classification. -/
@[expose] public section
namespace Rule30ConservationClassificationResearch
open Rule30ConservationCornerResearch Rule30ConservationWordResearch
open Rule30ConservationDescentResearch Rule30ConservationTrivialityResearch
open Rule30ConservationCycleResearch

theorem run_length (xs bs : List Bool) : (run xs bs).length=xs.length := by
  induction bs generalizing xs with
  | nil => rfl
  | cons b bs ih => rw [run,ih,shift_length]

theorem gradient_weight (n : Nat) (cost p : List Bool → Int)
    (hp : ∀ xs, xs.length=n → ∀ b, cost (xs++[b])=p xs-p (shift xs b))
    (xs bs : List Bool) (hl : xs.length=n) :
    weight cost xs bs=p xs-p (run xs bs) := by
  induction bs generalizing xs with
  | nil => simp [weight,run]
  | cons b bs ih =>
    rw [weight,hp xs hl b,ih _ (by rw [shift_length,hl])]
    change p xs-p (shift xs b)+(p (shift xs b)-p (run (shift xs b) bs))=
      p xs-p (run (shift xs b) bs)
    omega

theorem local_conserved_cyclic (m : Nat) (h p : List Bool → Int)
    (hc : Conserved m h p) : CyclicConserved m h := by
  have hp : ∀ xs, xs.length=m+7 → ∀ b,
      change m h (xs++[b])=p xs-p (shift xs b) := by
    intro xs hl b
    have hh:=conserved_word m h p hc (xs++[b]) (by simp [hl])
    rw [List.dropLast_concat] at hh
    unfold change shift
    rw [List.drop_one]
    omega
  intro xs hl bs hb
  have hh:=gradient_weight (m+7) (change m h) p hp xs bs hl
  rw [hb] at hh
  omega

theorem trivial_conserved (m : Nat) (hm : 0<m) (h : List Bool → Int)
    (ht : Trivial m h) : ∃ p, Conserved m h p := by
  obtain ⟨c,b,hb⟩:=ht
  let p := fun xs=>b (crop (m-1) xs)-b (image xs)
  refine ⟨p,conserved_of_word m h p ?_⟩
  intro xs hl
  have hi : (image xs).length=m := by rw [image_length,hl]; omega
  have hj : (crop m xs).length=m := crop_length m xs (by omega)
  have h1:=hb (image xs) hi
  have h2:=hb (crop m xs) hj
  have hit:=image_tail xs
  have hid:=image_dropLast xs
  have hct:=crop_tail (m-1) xs
  have hcd:=crop_dropLast (m-1) xs (by omega)
  have hm1 : m-1+1=m := by omega
  rw [hm1] at hct hcd
  have hn : xs≠[] := by intro he; simp [he] at hl
  have hc0:=crop_append (m-1) xs.dropLast
    (by rw [List.length_dropLast,hl]; omega) (xs.getLast hn)
  rw [List.dropLast_concat_getLast hn] at hc0
  rw [h1,h2,hit,←hid,hct,hcd]
  dsimp only [p]
  rw [←hc0]
  omega

/-- No hidden local-current premise and no bound on window width. -/
theorem cyclic_conserved_iff_trivial (m : Nat) (hm : 0<m) (h : List Bool → Int) :
    CyclicConserved m h ↔ Trivial m h := by
  constructor
  · exact cyclic_conserved_trivial m hm h
  · intro ht
    obtain ⟨p,hp⟩:=trivial_conserved m hm h ht
    exact local_conserved_cyclic m h p hp

theorem local_conserved_iff_trivial (m : Nat) (hm : 0<m) (h : List Bool → Int) :
    (∃ p, Conserved m h p) ↔ Trivial m h := by
  constructor
  · rintro ⟨p,hp⟩; exact conserved_trivial m hm h p hp
  · exact trivial_conserved m hm h

end Rule30ConservationClassificationResearch
