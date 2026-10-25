module
public import Rule30ConservationTrivialityResearch

/-! A uniform directed-word coboundary construction. The hypothesis is stated
directly as zero change of total density on every closed overlapping-word walk;
it does not assume the existence of a local current. -/
@[expose] public section
namespace Rule30ConservationCycleResearch
open Rule30ConservationCornerResearch Rule30ConservationWordResearch
open Rule30ConservationDescentResearch Rule30ConservationTrivialityResearch

def shift (xs : List Bool) (b : Bool) : List Bool := (xs++[b]).drop 1

def run : List Bool → List Bool → List Bool
  | xs, [] => xs
  | xs, b::bs => run (shift xs b) bs

def weight (cost : List Bool → Int) : List Bool → List Bool → Int
  | _, [] => 0
  | xs, b::bs => cost (xs++[b])+weight cost (shift xs b) bs

theorem shift_length (xs : List Bool) (b : Bool) : (shift xs b).length=xs.length := by
  simp [shift]

theorem run_append (xs bs cs : List Bool) : run xs (bs++cs)=run (run xs bs) cs := by
  induction bs generalizing xs with
  | nil => rfl
  | cons b bs ih => exact ih (shift xs b)

theorem weight_append (cost : List Bool → Int) (xs bs cs : List Bool) :
    weight cost xs (bs++cs)=weight cost xs bs+weight cost (run xs bs) cs := by
  induction bs generalizing xs with
  | nil => simp [weight,run]
  | cons b bs ih => simp only [List.cons_append,weight,run,ih]; omega

theorem run_formula (xs bs : List Bool) : run xs bs=(xs++bs).drop bs.length := by
  induction bs generalizing xs with
  | nil => simp [run]
  | cons b bs ih =>
    rw [run,ih]
    unfold shift
    rw [← List.drop_append_of_le_length (by simp : 1≤(xs++[b]).length)]
    rw [List.drop_drop]
    simp only [List.append_assoc,List.singleton_append,List.length_cons]
    congr 1
    omega

theorem run_reset (xs bs : List Bool) (hl : xs.length=bs.length) : run xs bs=bs := by
  rw [run_formula,←hl,List.drop_append_length]

def Balanced (n : Nat) (cost : List Bool → Int) : Prop :=
  ∀ xs, xs.length=n → ∀ bs, run xs bs=xs → weight cost xs bs=0

/-- Compare two closed walks through a common all-white state. Every width is
handled at once; no finite graph census is a premise. -/
theorem balanced_gradient (n : Nat) (cost : List Bool → Int) (hc : Balanced n cost) :
    ∃ p : List Bool → Int, ∀ xs, xs.length=n → ∀ b,
      cost (xs++[b])=p xs-p (shift xs b) := by
  let z := List.replicate n false
  let p := fun xs=>weight cost xs z
  refine ⟨p,?_⟩
  intro xs hl b
  have hz : z.length=n := List.length_replicate
  have hs : (shift xs b).length=n := by rw [shift_length,hl]
  have hr : run xs z=z := run_reset xs z (hl.trans hz.symm)
  have hsr : run (shift xs b) z=z := run_reset _ _ (hs.trans hz.symm)
  have hzx : run z xs=xs := run_reset _ _ (hz.trans hl.symm)
  have h0 : weight cost xs (z++xs)=0 := hc xs hl _ (by rw [run_append,hr,hzx])
  have h1 : weight cost xs (b::(z++xs))=0 := hc xs hl _ (by
    change run (shift xs b) (z++xs)=xs
    rw [run_append,hsr,hzx])
  rw [weight_append,hr] at h0
  change cost (xs++[b])+weight cost (shift xs b) (z++xs)=0 at h1
  rw [weight_append,hsr] at h1
  dsimp only [p]
  omega

def change (m : Nat) (h : List Bool → Int) (xs : List Bool) : Int :=
  h (image xs)-h (crop m xs)

/-- Global conservation along all closed walks of overlapping input windows. -/
def CyclicConserved (m : Nat) (h : List Bool → Int) : Prop := Balanced (m+7) (change m h)

theorem cyclic_conserved_local (m : Nat) (h : List Bool → Int)
    (hc : CyclicConserved m h) : ∃ p, Conserved m h p := by
  obtain ⟨p,hp⟩:=balanced_gradient (m+7) (change m h) hc
  refine ⟨p,conserved_of_word m h p ?_⟩
  intro xs hl
  have hn : xs≠[] := by intro he; simp [he] at hl
  have hx := List.dropLast_concat_getLast hn
  have hh:=hp xs.dropLast (by rw [List.length_dropLast,hl]; omega) (xs.getLast hn)
  rw [hx] at hh
  unfold shift at hh
  rw [hx] at hh
  change h (image xs)-h (crop m xs)=p xs.dropLast-p (xs.drop 1) at hh
  simpa only [List.drop_one] using (show h (image xs)=h (crop m xs)+p xs.dropLast-p (xs.drop 1) by omega)

theorem cyclic_conserved_trivial (m : Nat) (hm : 0<m) (h : List Bool → Int)
    (hc : CyclicConserved m h) : Trivial m h := by
  obtain ⟨p,hp⟩:=cyclic_conserved_local m h hc
  exact conserved_trivial m hm h p hp

end Rule30ConservationCycleResearch
