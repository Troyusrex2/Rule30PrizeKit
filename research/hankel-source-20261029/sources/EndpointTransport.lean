module
public import Ruliology.CellularAutomata.Rule30Prize
@[expose] public section
namespace EndpointTransport
open Ruliology.CellularAutomata.Rule30Jen

/-- Backward spatial decoding with two fixed right registers. -/
def fill (a b : Bool) : List Bool → Nat → Bool
  | [],0 => a
  | [],_+1 => b
  | y::ys,0 => rule y (fill a b ys 0) (fill a b ys 1)
  | _::ys,i+1 => fill a b ys i

theorem left_inverse (y a b : Bool) : rule (rule y a b) a b=y := by
  cases y <;> cases a <;> cases b <;> rfl

theorem fill_step (a b : Bool) (ys : List Bool) (i : Nat) (h : i<ys.length) :
    rule (fill a b ys i) (fill a b ys (i+1)) (fill a b ys (i+2))=ys[i] := by
  induction ys generalizing i with
  | nil => simp at h
  | cons y ys ih =>
    cases i with
    | zero => simp only [fill,List.getElem_cons_zero];exact left_inverse _ _ _
    | succ i =>
      simpa only [fill,List.getElem_cons_succ] using ih i (by simpa using h)

theorem fill_right0 (a b : Bool) (ys : List Bool) : fill a b ys ys.length=a := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simpa only [List.length_cons,fill] using ih

theorem fill_right1 (a b : Bool) (ys : List Bool) : fill a b ys (ys.length+1)=b := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simpa only [List.length_cons,fill] using ih

def rectangle (f : Bool → Bool → Bool) : Bool :=
  xor (xor (f false false) (f false true)) (xor (f true false) (f true true))

theorem rectangle_translate (f : Bool → Bool → Bool) (a : Bool) :
    rectangle (fun l r => f (xor l a) r)=rectangle f := by
  cases a with
  | false => rfl
  | true => exact Bool.xor_comm _ _

/-- A fixed target middle word, with white right registers, gives two independent
endpoint controls. This is a spatial statement, not temporal Hankel independence. -/
theorem endpoint_rectangle (ys : List Bool)
    (f : Bool → (Fin ys.length → Bool) → Bool → Bool) :
    rectangle (fun l r => f
      (rule l (fill false false ys 0) (fill false false ys 1))
      (fun i => rule (fill false false ys i.val) (fill false false ys (i.val+1))
        (fill false false ys (i.val+2)))
      (rule (fill false false ys ys.length) (fill false false ys (ys.length+1)) r))=
    rectangle (fun l r => f l (fun i => ys[i]) r) := by
  have hm : (fun i : Fin ys.length => rule (fill false false ys i.val)
      (fill false false ys (i.val+1)) (fill false false ys (i.val+2)))=
      (fun i : Fin ys.length => ys[i]) := by
    funext i
    exact fill_step false false ys i.val i.isLt
  rw [hm,fill_right0,fill_right1]
  change rectangle (fun l r => f (xor l _ ) (fun i => ys[i]) r)=_
  exact rectangle_translate (fun l r => f l (fun i => ys[i]) r)
    (fill false false ys 0 || fill false false ys 1)

/-- A separable left/right flux has zero endpoint rectangle. -/
theorem separable_rectangle (a b : Bool → Bool) (c : Bool) :
    rectangle (fun l r => xor (xor (a l) (b r)) c)=false := by
  dsimp only [rectangle]
  generalize a false=af
  generalize a true=atrue
  generalize b false=bf
  generalize b true=bt
  cases af <;> cases atrue <;> cases bf <;> cases bt <;> cases c <;> rfl

/-- Base case of the proposed charge classification, stated as a flux law. -/
theorem single_site_flux_trivial (rho : Bool → Bool) (j : Bool → Bool → Bool)
    (hn : rho false=false)
    (hf : ∀ l c r, xor (rho (rule l c r)) (rho c)=xor (j l c) (j c r)) :
    ∀ b, rho b=false := by
  have h001 := hf false false true
  have h010 := hf false true false
  have h011 := hf false true true
  have h110 := hf true true false
  clear hf
  dsimp only [rule] at h001 h010 h011 h110
  simp only [hn] at h001 h010 h011 h110
  intro b
  cases b with
  | false => exact hn
  | true =>
    generalize rho true=x at *
    generalize j false false=a at *
    generalize j false true=b at *
    generalize j true false=c at *
    generalize j true true=d at *
    cases x <;> cases a <;> cases b <;> cases c <;> cases d <;>
      simp_all only [Bool.xor_false,Bool.xor_true,
        Bool.or_false,Bool.or_true,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,Bool.true_eq_false]

/-- A normalized density with a genuine endpoint interaction cannot have a
separable flux on this decoded middle word. The global gauge/classification
argument is separate and is not asserted by this theorem. -/
theorem endpoint_obstructs_separable (ys : List Bool)
    (f : Bool → (Fin ys.length → Bool) → Bool → Bool)
    (hn : ∀ r, f false (fun i => ys[i]) r=false)
    (hd : f true (fun i => ys[i]) false ≠ f true (fun i => ys[i]) true) :
    ¬ ∃ a b : Bool → Bool, ∃ c : Bool, ∀ l r,
      f (rule l (fill false false ys 0) (fill false false ys 1))
        (fun i => rule (fill false false ys i.val) (fill false false ys (i.val+1))
          (fill false false ys (i.val+2)))
        (rule (fill false false ys ys.length) (fill false false ys (ys.length+1)) r)=
      xor (xor (a l) (b r)) c := by
  intro ⟨a,b,c,h⟩
  have he := endpoint_rectangle ys f
  have hf : (fun l r => f
      (rule l (fill false false ys 0) (fill false false ys 1))
      (fun i => rule (fill false false ys i.val) (fill false false ys (i.val+1))
        (fill false false ys (i.val+2)))
      (rule (fill false false ys ys.length) (fill false false ys (ys.length+1)) r))=
      (fun l r => xor (xor (a l) (b r)) c) := by
    funext l r
    exact h l r
  rw [hf] at he
  rw [separable_rectangle] at he
  dsimp only [rectangle] at he
  rw [hn false,hn true] at he
  generalize f true (fun i => ys[i]) false=u at *
  generalize f true (fun i => ys[i]) true=v at *
  cases u <;> cases v
  · exact hd rfl
  · cases he
  · cases he
  · exact hd rfl

end EndpointTransport
