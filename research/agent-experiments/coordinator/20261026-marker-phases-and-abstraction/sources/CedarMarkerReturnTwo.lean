import CedarSafetySoundness

/-! An exact all-width return-two criterion from delayed100 marker streams.
This is a Boolean carry proof, with no integer or2-adic library dependency. -/
namespace CedarMarkerReturnTwo
open CedarSafetySoundness
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def carry (p r s : Bool) : Bool := (p || r) || s
def marker (p r s : Bool) : Bool := s && (!r) && (!p)
def marks (p r s : Bool) : List Bool → List Bool
  | [] => []
  | v :: vs => marker p r s :: marks v p r vs
def marked (xs : List Bool) : List Bool := marks false false false xs
def AllZero : List Bool → Prop
  | [] => True
  | v :: vs => v = false ∧ AllZero vs
def Disjoint : List Bool → List Bool → Prop
  | [], [] => True
  | a :: as, b :: bs => (a && b) = false ∧ Disjoint as bs
  | _, _ => False

theorem head_equivalence : ∀ p r s pp rr ss v : Bool,
    carry p r s = carry pp rr ss →
    (xor (xor v (p || r)) (pp || rr) = v ↔ marker p r s = marker pp rr ss) := by
  decide +kernel

theorem next_carry : ∀ p r pp rr v : Bool,
    xor (xor v (p || r)) (pp || rr) = v →
    carry v p r = carry (xor v (p || r)) pp rr := by
  decide +kernel

theorem disjoint_head : ∀ p r s pp rr ss : Bool,
    pp = xor p (r || s) → (marker p r s && marker pp rr ss) = false := by
  decide +kernel

theorem return_iff_marker_equal (xs : List Bool) :
    ∀ p r s pp rr ss : Bool, carry p r s = carry pp rr ss →
    (change pp rr (change p r xs) = xs ↔
      marks p r s xs = marks pp rr ss (change p r xs)) := by
  induction xs with
  | nil => intro p r s pp rr ss hc; simp [change,marks]
  | cons v vs ih =>
    intro p r s pp rr ss hc
    let y := xor v (p || r)
    let z := xor y (pp || rr)
    have he : z = v ↔ marker p r s = marker pp rr ss :=
      head_equivalence p r s pp rr ss v hc
    constructor
    · intro h
      have hcns : z :: change y pp (change v p vs) = v :: vs := h
      obtain ⟨hz,ht⟩ := List.cons.inj hcns
      have hn : carry v p r = carry y pp rr := next_carry p r pp rr v hz
      have hm := (ih v p r y pp rr hn).mp ht
      change marker p r s :: marks v p r vs =
        marker pp rr ss :: marks y pp rr (change v p vs)
      rw [he.mp hz,hm]
    · intro h
      have hcns : marker p r s :: marks v p r vs =
          marker pp rr ss :: marks y pp rr (change v p vs) := h
      obtain ⟨hq,ht⟩ := List.cons.inj hcns
      have hz : z = v := he.mpr hq
      have hn : carry v p r = carry y pp rr := next_carry p r pp rr v hz
      have hr := (ih v p r y pp rr hn).mpr ht
      change z :: change y pp (change v p vs) = v :: vs
      rw [hz,hr]

theorem marker_streams_disjoint (xs : List Bool) :
    ∀ p r s pp rr ss : Bool, pp = xor p (r || s) →
    Disjoint (marks p r s xs) (marks pp rr ss (change p r xs)) := by
  induction xs with
  | nil => intro p r s pp rr ss hp; trivial
  | cons v vs ih =>
    intro p r s pp rr ss hp
    exact ⟨disjoint_head p r s pp rr ss hp,
      ih v p r (xor v (p || r)) pp rr rfl⟩

theorem disjoint_equal_iff_zero (as bs : List Bool) (hd : Disjoint as bs) :
    as = bs ↔ AllZero as ∧ AllZero bs := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [AllZero]
    | cons b bs => exact False.elim hd
  | cons a as ih =>
    cases bs with
    | nil => exact False.elim hd
    | cons b bs =>
      constructor
      · intro h
        obtain ⟨hab,ht⟩ := List.cons.inj h
        have ha : a = false := by
          have hh := hd.1
          rw [← hab] at hh
          cases a <;> simp_all
        have hb : b = false := hab.symm.trans ha
        obtain ⟨za,zb⟩ := (ih bs hd.2).mp ht
        exact ⟨⟨ha,za⟩,⟨hb,zb⟩⟩
      · rintro ⟨⟨ha,za⟩,⟨hb,zb⟩⟩
        have ht := (ih bs hd.2).mpr ⟨za,zb⟩
        rw [ha,hb,ht]

theorem marked_disjoint (xs : List Bool) : Disjoint (marked xs) (marked (F xs)) :=
  marker_streams_disjoint xs false false false false false false rfl

/-- Exact finite-white return-two criterion, including all small widths.
No safety assumption occurs. The first three entries of marked are zero;
its entry k+3 is the100 marker beginning at spatial position k. -/
theorem return_two_iff_markers_zero (xs : List Bool) :
    evolution 2 xs = xs ↔ AllZero (marked xs) ∧ AllZero (marked (F xs)) := by
  have he := return_iff_marker_equal xs false false false false false false rfl
  have hz := disjoint_equal_iff_zero (marked xs) (marked (F xs)) (marked_disjoint xs)
  exact he.trans hz

end CedarMarkerReturnTwo
