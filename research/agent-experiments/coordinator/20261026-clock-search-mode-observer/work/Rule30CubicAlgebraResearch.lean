module
public import Rule30CubicCertificateData

/-! Generic cubic-annihilation transfer through a zero-start xor integral.
No specific certificate, clock, or Rule 30 observer is asserted here. -/
@[expose] public section
namespace Rule30CubicAlgebraResearch
open Rule30CubicCertificateData (xorList)
set_option maxHeartbeats 4000000

theorem xor_grid (a b c d : Bool) :
    xor (xor a b) (xor c d)=xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem sum_congr {α : Type} (xs : List α) (f g : α → Bool) :
    (∀ x, x∈xs → f x=g x) → xorList xs f=xorList xs g := by
  induction xs with
  | nil => intro _;rfl
  | cons a xs ih =>
    intro h
    simp only [xorList]
    rw [h a (by simp),ih (fun x hx => h x (by simp [hx]))]

theorem sum_false {α : Type} (xs : List α) : xorList xs (fun _ => false)=false := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [xorList,ih];rfl

theorem sum_xor {α : Type} (xs : List α) (f g : α → Bool) :
    xorList xs (fun x => xor (f x) (g x))=xor (xorList xs f) (xorList xs g) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [xorList,ih];exact xor_grid _ _ _ _

theorem and3_first (a b c d : Bool) :
    (xor a b && c && d)=xor (a && c && d) (b && c && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
theorem and3_middle (a b c d : Bool) :
    (a && xor b c && d)=xor (a && b && d) (a && c && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
theorem and3_last (a b c d : Bool) :
    (a && b && xor c d)=xor (a && b && c) (a && b && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

variable {α : Type} (xs : List α) (h r : α → Nat → Bool)
  (hzero : ∀ x, h x 0=false)
  (hstep : ∀ x t, h x (t+1)=xor (h x t) (r x t))
  (hr : ∀ a b c, xorList xs (fun x => r x a && r x b && r x c)=false)

include hzero hstep hr in
theorem head_driver_driver_zero (t a b : Nat) :
    xorList xs (fun x => h x t && r x a && r x b)=false := by
  induction t with
  | zero =>
    have he : (fun x => h x 0 && r x a && r x b)=(fun _ => false) := by
      funext x;rw [hzero x];rfl
    rw [he];exact sum_false xs
  | succ t ih =>
    calc
      xorList xs (fun x => h x (t+1) && r x a && r x b) =
          xorList xs (fun x => xor (h x t && r x a && r x b)
            (r x t && r x a && r x b)) := by
        apply sum_congr;intro x _;rw [hstep x t];exact and3_first _ _ _ _
      _ = xor (xorList xs (fun x => h x t && r x a && r x b))
            (xorList xs (fun x => r x t && r x a && r x b)) := sum_xor _ _ _
      _ = false := by rw [ih,hr t a b];rfl

include hzero hstep hr in
theorem head_head_driver_zero (t u a : Nat) :
    xorList xs (fun x => h x t && h x u && r x a)=false := by
  induction u with
  | zero =>
    have he : (fun x => h x t && h x 0 && r x a)=(fun _ => false) := by
      funext x;rw [hzero x];cases h x t <;> rfl
    rw [he];exact sum_false xs
  | succ u ih =>
    calc
      xorList xs (fun x => h x t && h x (u+1) && r x a) =
          xorList xs (fun x => xor (h x t && h x u && r x a)
            (h x t && r x u && r x a)) := by
        apply sum_congr;intro x _;rw [hstep x u];exact and3_middle _ _ _ _
      _ = xor (xorList xs (fun x => h x t && h x u && r x a))
            (xorList xs (fun x => h x t && r x u && r x a)) := sum_xor _ _ _
      _ = false := by rw [ih,head_driver_driver_zero xs h r hzero hstep hr t u a];rfl

include hzero hstep hr in
theorem head_triples_zero (t u v : Nat) :
    xorList xs (fun x => h x t && h x u && h x v)=false := by
  induction v with
  | zero =>
    have he : (fun x => h x t && h x u && h x 0)=(fun _ => false) := by
      funext x;rw [hzero x];cases h x t <;> cases h x u <;> rfl
    rw [he];exact sum_false xs
  | succ v ih =>
    calc
      xorList xs (fun x => h x t && h x u && h x (v+1)) =
          xorList xs (fun x => xor (h x t && h x u && h x v)
            (h x t && h x u && r x v)) := by
        apply sum_congr;intro x _;rw [hstep x v];exact and3_last _ _ _ _
      _ = xor (xorList xs (fun x => h x t && h x u && h x v))
            (xorList xs (fun x => h x t && h x u && r x v)) := sum_xor _ _ _
      _ = false := by rw [ih,head_head_driver_zero xs h r hzero hstep hr t u v];rfl

def monomial (f : Nat → Bool) : List Nat → Bool
  | [] => true
  | t::ts => f t && monomial f ts

def polynomial (f : Nat → Bool) (terms : List (List Nat)) : Bool :=
  xorList terms (monomial f)

include hzero hstep hr in
theorem head_monomial_zero
    (heven : xorList xs (fun _ => true)=false) (ts : List Nat) (ht : ts.length≤3) :
    xorList xs (fun x => monomial (h x) ts)=false := by
  cases ts with
  | nil => exact heven
  | cons t ts =>
    cases ts with
    | nil =>
      simpa only [monomial,Bool.and_true,Bool.and_assoc,Bool.and_self] using
        head_triples_zero xs h r hzero hstep hr t t t
    | cons u ts =>
      cases ts with
      | nil =>
        simpa only [monomial,Bool.and_true,Bool.and_assoc,Bool.and_self] using
          head_triples_zero xs h r hzero hstep hr t u u
      | cons v ts =>
        cases ts with
        | nil =>
          simpa only [monomial,Bool.and_true,Bool.and_assoc] using
            head_triples_zero xs h r hzero hstep hr t u v
        | cons w ts => simp only [List.length_cons] at ht;omega

include hzero hstep hr in
theorem head_polynomial_zero (heven : xorList xs (fun _ => true)=false)
    (terms : List (List Nat)) :
    (∀ ts, ts∈terms → ts.length≤3) →
      xorList xs (fun x => polynomial (h x) terms)=false := by
  induction terms with
  | nil => intro _;exact sum_false xs
  | cons ts terms ih =>
    intro ht
    have hm := head_monomial_zero xs h r hzero hstep hr heven ts (ht ts (by simp))
    have hp := ih (fun us hu => ht us (by simp [hu]))
    calc
      xorList xs (fun x => polynomial (h x) (ts::terms)) =
          xorList xs (fun x => xor (monomial (h x) ts) (polynomial (h x) terms)) := rfl
      _ = xor (xorList xs (fun x => monomial (h x) ts))
            (xorList xs (fun x => polynomial (h x) terms)) := sum_xor _ _ _
      _ = false := by rw [hm,hp];rfl

include hzero hstep hr in
theorem no_cubic_head_decoder (heven : xorList xs (fun _ => true)=false)
    (target : α → Bool) (htarget : xorList xs target=true)
    (terms : List (List Nat)) (ht : ∀ ts, ts∈terms → ts.length≤3) :
    ¬(∀ x, x∈xs → polynomial (h x) terms=target x) := by
  intro he
  have hz := head_polynomial_zero xs h r hzero hstep hr heven terms ht
  have heq := sum_congr xs (fun x => polynomial (h x) terms) target he
  rw [heq,htarget] at hz
  cases hz

end Rule30CubicAlgebraResearch
