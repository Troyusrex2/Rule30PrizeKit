module
public import Rule30Equivalents.IntegerRows
public import Rule30Equivalents.TFunction
public import Ruliology.CellularAutomata.Rule30Prize

/-! Physical finite-horizon counterexample retaining canonical backgrounds,
left edge, initial subset and zero center. P1 and all-time observability remain
open. Prior pulse/locality and integer-row checkpoint arguments are reused
from Troy Lowry's earlier verified research; no new axiom or native decision.
-/
@[expose] public section
namespace Rule30SensorClosureResearch
open Ruliology.CellularAutomata
open Rule30Jen (rule cell)
open Rule30Realization (evol)
open Rule30Equivalents.IntegerRows
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def step (x : Int → Bool) (p : Int) := rule (x (p-1)) (x p) (x (p+1))

def pulseTarget (U p : Int) : Bool := decide (p = -1 ∨ p = 0 ∨ p = 1 ∨ p = U)

def unit (U p : Int) : Bool := decide (p = U)

def diffStep (A B h : Int → Bool) (p : Int) : Bool :=
  xor (xor (h (p-1)) ((! B (p+1)) && h p)) ((! A p) && h (p+1))

def Subset (A B h : Int → Bool) : Prop := ∀ p, (h p && xor (A p) (B p)) = h p

def Common (A B h : Int → Bool) : Prop := ∀ p,
  (xor (A (p+1)) (B (p+1)) && h p) = (xor (A p) (B p) && h (p+1))

theorem evol_local (x y : Int → Bool) (t : Nat) (p : Int)
    (h : ∀ q, p-t ≤ q → q ≤ p+t → x q=y q) : evol x t p=evol y t p := by
  induction t generalizing p with
  | zero => exact h p (by omega) (by omega)
  | succ t ih =>
    change rule (evol x t (p-1)) (evol x t p) (evol x t (p+1)) =
      rule (evol y t (p-1)) (evol y t p) (evol y t (p+1))
    rw [ih (p-1) (fun q hq hq' => h q (by omega) (by omega)),
      ih p (fun q hq hq' => h q (by omega) (by omega)),
      ih (p+1) (fun q hq hq' => h q (by omega) (by omega))]

theorem evol_white (t : Nat) (p : Int) : evol (fun _ => false) t p=false := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih => simp [evol, ih, rule]

theorem pulse_evol (U : Int) (t : Nat) (p : Int) : evol (unit U) t p=cell t (p-U) := by
  induction t generalizing p with
  | zero =>
    change decide (p=U)=decide (p-U=0)
    have he : (p=U) ↔ (p-U=0) := by omega
    simp only [he]
  | succ t ih =>
    change rule (evol (unit U) t (p-1)) (evol (unit U) t p) (evol (unit U) t (p+1)) = _
    rw [ih, ih, ih]
    change rule (cell t (p-1-U)) (cell t (p-U)) (cell t (p+1-U)) =
      rule (cell t (p-U-1)) (cell t (p-U)) (cell t (p-U+1))
    congr 2 <;> omega

theorem pulse_support (U : Int) (t : Nat) (p : Int) (hp : evol (unit U) t p=true) :
    U-t ≤ p ∧ p ≤ U+t := by
  rw [pulse_evol] at hp
  constructor
  · by_contra hn
    have hw := Rule30Jen.cell_eq_false_of_lt t (p-U) (by omega)
    rw [hw] at hp; cases hp
  · by_contra hn
    have hw := Rule30Diagonals.cell_eq_false_of_gt t (p-U) (by omega)
    rw [hw] at hp; cases hp


theorem physical_local : ∀ ac ar bc br hl hc hr : Bool,
    ((hc=true ∨ hr=true) → ac=hc ∧ ar=hr ∧ bc=false ∧ br=false) →
    xor (xor hl ((!br) && hc)) ((!ac) && hr) = rule hl hc hr ∧
    ((xor ar br) && hc) = ((xor ac bc) && hr) := by decide +kernel

theorem local_mode (A B h : Int → Bool)
    (hlocal : ∀ p, (h p=true ∨ h (p+1)=true) →
      A p=h p ∧ A (p+1)=h (p+1) ∧ B p=false ∧ B (p+1)=false) :
    (∀ p, diffStep A B h p=step h p) ∧ Common A B h := by
  constructor <;> intro p
  · exact (physical_local (A p) (A (p+1)) (B p) (B (p+1))
      (h (p-1)) (h p) (h (p+1)) (hlocal p)).1
  · exact (physical_local (A p) (A (p+1)) (B p) (B (p+1))
      (h (p-1)) (h p) (h (p+1)) (hlocal p)).2


theorem restart (U t : Nat) (p : Int) : evol (cell U) t p=cell (U+t) p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    change rule (evol (cell U) t (p-1)) (evol (cell U) t p)
      (evol (cell U) t (p+1)) = _
    rw [ih, ih, ih]
    rfl


/-! All equations use physical positions. No hypothesis about a backward
common-field constraint is needed for the nonlifting conclusion. -/

theorem prefix_agreement (U E H t : Nat)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (he : 2*H+1 ≤ E) (ht : t ≤ H)
    (p : Int) (hp : (U : Int)-t-1 ≤ p) :
    cell (U+t) p=evol (unit U) t p := by
  rw [← restart]
  apply evol_local
  intro q hq _
  apply hgap
  omega

theorem pulse_mode (U V E H t : Nat)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (he : 2*H+1 ≤ E) (hUV : V+2*H+3 ≤ U) (ht : t ≤ H) :
    (∀ p, diffStep (cell (U+t)) (cell (V+t)) (evol (unit U) t) p =
      evol (unit U) (t+1) p) ∧
    Common (cell (U+t)) (cell (V+t)) (evol (unit U) t) := by
  apply local_mode
  intro p hb
  have hp : (U : Int)-t-1 ≤ p := by
    rcases hb with hb | hb
    · have := pulse_support U t p hb; omega
    · have := pulse_support U t (p+1) hb; omega
  refine ⟨prefix_agreement U E H t hgap he ht p hp,
    prefix_agreement U E H t hgap he ht (p+1) (by omega), ?_, ?_⟩
  · apply Rule30Diagonals.cell_eq_false_of_gt; omega
  · apply Rule30Diagonals.cell_eq_false_of_gt; omega

theorem diff_xor_local : ∀ al ar br hl hc hr kl kc kr : Bool,
    xor (xor (xor hl kl) ((!br) && xor hc kc)) ((!al) && xor hr kr) =
    xor (xor (xor hl ((!br) && hc)) ((!al) && hr))
        (xor (xor kl ((!br) && kc)) ((!al) && kr)) := by decide +kernel

theorem diff_xor (A B h k : Int → Bool) (p : Int) :
    diffStep A B (fun q => xor (h q) (k q)) p =
      xor (diffStep A B h p) (diffStep A B k p) :=
  diff_xor_local (A p) (A (p+1)) (B (p+1))
    (h (p-1)) (h p) (h (p+1)) (k (p-1)) (k p) (k (p+1))

theorem actual_local : ∀ al ac ar bl bc br : Bool,
    xor (xor (xor al bl) ((!br) && xor ac bc)) ((!ac) && xor ar br) =
      xor (rule al ac ar) (rule bl bc br) := by decide +kernel

theorem actual_difference (U V t : Nat) (p : Int) :
    diffStep (cell (U+t)) (cell (V+t))
      (fun q => xor (cell (U+t) q) (cell (V+t) q)) p =
      xor (cell (U+(t+1)) p) (cell (V+(t+1)) p) := by
  rw [show U+(t+1)=(U+t)+1 by omega,show V+(t+1)=(V+t)+1 by omega]
  exact actual_local
    (cell (U+t) (p-1)) (cell (U+t) p) (cell (U+t) (p+1))
    (cell (V+t) (p-1)) (cell (V+t) p) (cell (V+t) (p+1))

theorem common_flip_local : ∀ ac ar bc br hc hr : Bool,
    ((xor ar br) && hc) = ((xor ac bc) && hr) →
    ((xor ar br) && xor (xor ac bc) hc) =
      ((xor ac bc) && xor (xor ar br) hr) := by decide +kernel

def field (U V t : Nat) (p : Int) : Bool :=
  xor (xor (cell (U+t) p) (cell (V+t) p)) (evol (unit U) t p)

theorem field_mode (U V E H t : Nat)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (he : 2*H+1 ≤ E) (hUV : V+2*H+3 ≤ U) (ht : t ≤ H) :
    (∀ p, diffStep (cell (U+t)) (cell (V+t)) (field U V t) p =
      field U V (t+1) p) ∧
    Common (cell (U+t)) (cell (V+t)) (field U V t) := by
  obtain ⟨hd,hw⟩ := pulse_mode U V E H t hgap he hUV ht
  constructor
  · intro p
    unfold field
    rw [diff_xor, actual_difference, hd]
  · intro p
    exact common_flip_local _ _ _ _ _ _ (hw p)

theorem field_subset (U V : Nat) (hUV : V < U) :
    Subset (cell U) (cell V) (field U V 0) := by
  intro p
  by_cases hp : p=U
  · subst p
    have ha : cell U (U : Int)=true := by
      simpa [Rule30Diagonals.R] using Rule30Diagonals.R_zero U
    have hb := Rule30Diagonals.cell_eq_false_of_gt V (U : Int) (by omega)
    simp [field, evol, unit, ha, hb]
  · simp [field, evol, unit, hp]

theorem field_left (U V t : Nat) (hUV : V < U) :
    field U V t (-(U : Int)-t)=true := by
  have ha : cell (U+t) (-(U : Int)-t)=true := by
    rw [show -(U : Int)-t = -((U+t : Nat) : Int) by omega]
    exact Rule30Jen.cell_left_edge (U+t)
  have hb := Rule30Jen.cell_eq_false_of_lt (V+t) (-(U : Int)-t) (by omega)
  have hp : evol (unit U) t (-(U : Int)-t)=false := by
    cases hc : evol (unit U) t (-(U : Int)-t) with
    | false => rfl
    | true => have := pulse_support U t (-(U : Int)-t) hc; omega
  simp [field,ha,hb,hp]

theorem field_center (U V H t : Nat) (hU : H < U) (ht : t ≤ H)
    (heq : cell (U+t) 0=cell (V+t) 0) : field U V t 0=false := by
  have hp : evol (unit U) t 0=false := by
    cases hc : evol (unit U) t 0 with
    | false => rfl
    | true => have := pulse_support U t 0 hc; omega
  simp [field,heq,hp]

theorem field_right_white (U V E : Nat) (hVU : V ≤ U)
    (hq : U-V ≤ E)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (p : Int) (hp : (V : Int)<p) : field U V 0 p=false := by
  have ha := hgap p (by omega)
  have hb := Rule30Diagonals.cell_eq_false_of_gt V p hp
  simp [field,evol,ha,hb]

theorem field_right_black (U V E : Nat) (hVU : V < U)
    (hq : U-V ≤ E)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p) :
    field U V 0 V=true := by
  have ha := hgap V (by omega)
  have hb : cell V (V : Int)=true := by
    simpa [Rule30Diagonals.R] using Rule30Diagonals.R_zero V
  simp [field,evol,ha,hb,unit,show (V : Int)≠U by omega]

/-- The rightmost bit of every upper-bounded auxiliary field advances by one.
This backward version does not assume W or physical coefficient evolution. -/
theorem preimage_right_edge (A B g h : Int → Bool) (U V : Nat)
    (hVU : V ≤ U) (hg : ∀ p : Int, (U : Int) ≤ p → g p=false)
    (hh : ∀ p : Int, (V : Int)<p → h p=false) (hb : h V=true)
    (hs : ∀ p, diffStep A B g p=h p) : g ((V : Int)-1)=true := by
  have key : ∀ n : Nat, n ≤ U-V →
      g ((U : Int)-n)=false ∧ g ((U : Int)-n+1)=false := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hg U (by omega),hg ((U : Int)+1) (by omega)⟩
    | succ n ih =>
      intro hn
      obtain ⟨hc,hr⟩ := ih (by omega)
      have hd := hs ((U : Int)-n)
      have hz := hh ((U : Int)-n) (by omega)
      have hl : g ((U : Int)-n-1)=false := by
        simpa [diffStep,hc,hr,hz] using hd
      constructor
      · rw [show (U : Int)-((n+1 : Nat) : Int)=(U : Int)-n-1 by omega]
        exact hl
      · rw [show (U : Int)-((n+1 : Nat) : Int)+1=(U : Int)-n by omega]
        exact hc
  obtain ⟨hc,hr⟩ := key (U-V) (by omega)
  have pos : (U : Int)-((U-V : Nat) : Int)=V := by omega
  rw [pos] at hc hr
  have hd := hs (V : Int)
  simpa [diffStep,hc,hr,hb] using hd

theorem field_nonlift (U V E : Nat) (hV : 1 ≤ V) (hVU : V < U)
    (hq : U-V ≤ E)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (hprior : cell (U-1) ((V : Int)-1)=true) :
    ¬ ∃ g : Int → Bool, Subset (cell (U-1)) (cell (V-1)) g ∧
      ∀ p, diffStep (cell (U-1)) (cell (V-1)) g p=field U V 0 p := by
  rintro ⟨g,hsub,hstep⟩
  have upper : ∀ p : Int, (U : Int) ≤ p → g p=false := by
    intro p hp
    have ha := Rule30Diagonals.cell_eq_false_of_gt (U-1) p (by omega)
    have hb := Rule30Diagonals.cell_eq_false_of_gt (V-1) p (by omega)
    have hs := hsub p
    cases hc : g p <;> simp_all
  have forced := preimage_right_edge _ _ g (field U V 0) U V (by omega) upper
    (field_right_white U V E (by omega) hq hgap)
    (field_right_black U V E hVU hq hgap) hstep
  have hb : cell (V-1) ((V : Int)-1)=true := by
    rw [← show ((V-1 : Nat) : Int)=(V : Int)-1 by omega]
    simpa [Rule30Diagonals.R] using Rule30Diagonals.R_zero (V-1)
  have bad := hsub ((V : Int)-1)
  simp [hprior,hb,forced] at bad

theorem field_white_left (U V t : Nat) (hVU : V ≤ U) (p : Int)
    (hp : p < -(U : Int)-t) : field U V t p=false := by
  have ha := Rule30Jen.cell_eq_false_of_lt (U+t) p (by omega)
  have hb := Rule30Jen.cell_eq_false_of_lt (V+t) p (by omega)
  have hc : evol (unit U) t p=false := by
    cases hx : evol (unit U) t p with
    | false => rfl
    | true => have := pulse_support U t p hx; omega
  simp [field,ha,hb,hc]

theorem field_white_right (U V t : Nat) (hVU : V ≤ U) (p : Int)
    (hp : (U : Int)+t < p) : field U V t p=false := by
  have ha := Rule30Diagonals.cell_eq_false_of_gt (U+t) p (by omega)
  have hb := Rule30Diagonals.cell_eq_false_of_gt (V+t) p (by omega)
  have hc : evol (unit U) t p=false := by
    cases hx : evol (unit U) t p with
    | false => rfl
    | true => have := pulse_support U t p hx; omega
  simp [field,ha,hb,hc]

/-- Continue by D for all time, including beyond the finite W/sensor window. -/
def evolved (U V : Nat) : Nat → Int → Bool
  | 0 => field U V 0
  | t+1 => fun p => diffStep (cell (U+t)) (cell (V+t)) (evolved U V t) p

theorem evolved_eq (U V E H t : Nat)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (he : 2*H+1 ≤ E) (hUV : V+2*H+3 ≤ U) (ht : t ≤ H+1) :
    evolved U V t=field U V t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext p
    change diffStep (cell (U+t)) (cell (V+t)) (evolved U V t) p=field U V (t+1) p
    rw [ih (by omega)]
    exact (field_mode U V E H t hgap he hUV (by omega)).1 p

/-! The following finite data select an example with the sensor retained.
Every checkpoint is a kernel computation of the official integer recurrence. -/

def rowStep (x : Nat) : Nat := x ^^^ ((2*x) ||| (4*x))
def advance : Nat → Nat → Nat
  | 0,x => x
  | k+1,x => rowStep (advance k x)

theorem a_add (n k : Nat) : a (n+k)=advance k (a n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change rowStep (a (n+k))=rowStep (advance k (a n))
    rw [ih]

theorem checkpoint_0 : a 0=1 := rfl

theorem checkpoint_32 : a 32=0x191cf1e88c4612a01 := by
  calc a 32=advance 32 (a 0) := a_add 0 32
    _=advance 32 0x1 := congrArg (advance 32) checkpoint_0
    _=0x191cf1e88c4612a01 := by decide +kernel

theorem checkpoint_64 : a 64=0x191cf1e8fd0fd708550e89be8bf6e8001 := by
  calc a 64=advance 32 (a 32) := a_add 32 32
    _=advance 32 0x191cf1e88c4612a01 := congrArg (advance 32) checkpoint_32
    _=0x191cf1e8fd0fd708550e89be8bf6e8001 := by decide +kernel

theorem checkpoint_96 : a 96=0x191cf1e8fd0fce8c15e9cd799762536820ae20ecd0774aa01 := by
  calc a 96=advance 32 (a 64) := a_add 64 32
    _=advance 32 0x191cf1e8fd0fd708550e89be8bf6e8001 := congrArg (advance 32) checkpoint_64
    _=0x191cf1e8fd0fce8c15e9cd799762536820ae20ecd0774aa01 := by decide +kernel

theorem checkpoint_128 : a 128=0x191cf1e8fd0fce8c17a8e8c546227e9b5bae66fe24ec09a7737f6269ed1970001 := by
  calc a 128=advance 32 (a 96) := a_add 96 32
    _=advance 32 0x191cf1e8fd0fce8c15e9cd799762536820ae20ecd0774aa01 := congrArg (advance 32) checkpoint_96
    _=0x191cf1e8fd0fce8c17a8e8c546227e9b5bae66fe24ec09a7737f6269ed1970001 := by decide +kernel

theorem checkpoint_160 : a 160=0x191cf1e8fd0fce8c17a8e8c50965d1833524b7280cd9722acde60c77cbb2d382eb0ccb5ecdfec2a01 := by
  calc a 160=advance 32 (a 128) := a_add 128 32
    _=advance 32 0x191cf1e8fd0fce8c17a8e8c546227e9b5bae66fe24ec09a7737f6269ed1970001 := congrArg (advance 32) checkpoint_128
    _=0x191cf1e8fd0fce8c17a8e8c50965d1833524b7280cd9722acde60c77cbb2d382eb0ccb5ecdfec2a01 := by decide +kernel

theorem checkpoint_192 : a 192=0x191cf1e8fd0fce8c17a8e8c50965d37eaabeaaf8d0ff63f1541859191ef40027ef802dbbdbdfb7ccf51b5460cc7e78001 := by
  calc a 192=advance 32 (a 160) := a_add 160 32
    _=advance 32 0x191cf1e8fd0fce8c17a8e8c50965d1833524b7280cd9722acde60c77cbb2d382eb0ccb5ecdfec2a01 := congrArg (advance 32) checkpoint_160
    _=0x191cf1e8fd0fce8c17a8e8c50965d37eaabeaaf8d0ff63f1541859191ef40027ef802dbbdbdfb7ccf51b5460cc7e78001 := by decide +kernel

theorem checkpoint_224 : a 224=0x191cf1e8fd0fce8c17a8e8c50965d37eaabeaafeb03e50d9964d48e5f2a3d52791c8c4e98eef131fee6e374cc8088b8fa29744682d987aa01 := by
  calc a 224=advance 32 (a 192) := a_add 192 32
    _=advance 32 0x191cf1e8fd0fce8c17a8e8c50965d37eaabeaaf8d0ff63f1541859191ef40027ef802dbbdbdfb7ccf51b5460cc7e78001 := congrArg (advance 32) checkpoint_192
    _=0x191cf1e8fd0fce8c17a8e8c50965d37eaabeaafeb03e50d9964d48e5f2a3d52791c8c4e98eef131fee6e374cc8088b8fa29744682d987aa01 := by decide +kernel

theorem checkpoint_256 : a 256=0x191cf1e8fd0fce8c17a8e8c50965d37eaabeaafeb03e518b9412d3f08625ebc215ebf190b8f44dd85ff3e7c4e83324a15377485312386cfb730b1b9f889000001 := by
  calc a 256=advance 32 (a 224) := a_add 224 32
    _=advance 32 0x191cf1e8fd0fce8c17a8e8c50965d37eaabeaafeb03e50d9964d48e5f2a3d52791c8c4e98eef131fee6e374cc8088b8fa29744682d987aa01 := congrArg (advance 32) checkpoint_224
    _=0x191cf1e8fd0fce8c17a8e8c50965d37eaabeaafeb03e518b9412d3f08625ebc215ebf190b8f44dd85ff3e7c4e83324a15377485312386cfb730b1b9f889000001 := by decide +kernel



theorem gap_256 (p : Int) (hp : (256 : Int)-23 ≤ p) :
    cell 256 p=unit 256 p := by
  by_cases hout : 256 < p
  · rw [Rule30Diagonals.cell_eq_false_of_gt _ _ hout]
    symm
    simp only [unit,decide_eq_false_iff_not]; omega
  · let j : Nat := (256-p).toNat
    have hj : j < 24 := by dsimp [j]; omega
    have heq : (256 : Int)-j=p := by dsimp [j]; omega
    have low : (a 256)%2^24=1 := by rw [checkpoint_256] <;> decide +kernel
    have bit := congrArg (fun x : Nat => x.testBit j) low
    simp only [Nat.testBit_mod_two_pow,hj,decide_true,Bool.true_and,testBit_a] at bit
    norm_num only [Nat.cast_ofNat] at bit
    rw [heq] at bit
    rw [bit]
    by_cases hz : j=0
    · have hp' : p=256 := by omega
      simp [unit,hz,hp']
    · have hp' : p≠256 := by omega
      simp only [unit,hp',decide_false]
      cases h : j with
      | zero => exact False.elim (hz h)
      | succ j => simp [Nat.testBit_succ]

theorem prior_255_at_236 : cell 255 236=true := by
  have hb := testBit_a 255 19
  have ha : a 255=advance 31 (a 224) := a_add 224 31
  rw [ha,checkpoint_224] at hb
  exact hb.symm.trans (by decide +kernel)

theorem center_agreement_6 : ∀ t : Nat, t ≤ 6 → cell (256+t) 0=cell (237+t) 0 := by
  have h : ∀ t : Fin 7,
      (advance t (a 256)).testBit (256+t) =
      (advance (13+t) (a 224)).testBit (237+t) := by
    rw [checkpoint_256,checkpoint_224]
    decide +kernel
  intro t ht
  have hh := h ⟨t,by omega⟩
  rw [← a_add 256 t,← a_add 224 (13+t)] at hh
  simpa only [testBit_a,show 224+(13+t)=237+t by omega,Int.sub_self] using hh

/-- A finite sensor-compatible obstruction to the proposed one-step closure.
The previous-subset failure holds even without imposing previous W. This is
not an all-time common-field counterexample and proves no prize statement. -/
theorem finite_sensor_nonlift : ∃ h : Nat → Int → Bool,
    Subset (cell 256) (cell 237) (h 0) ∧
    (∀ p : Int, p < -256 ∨ 256 < p → h 0 p=false) ∧
    (∀ t, t ≤ 6 → h t (-(256 : Int)-t)=true ∧
      ∀ p, p < -(256 : Int)-t → h t p=false) ∧
    (∀ t, t ≤ 6 → h t 0=false) ∧
    (∀ t, t ≤ 6 → Common (cell (256+t)) (cell (237+t)) (h t)) ∧
    (∀ t p, h (t+1) p=diffStep (cell (256+t)) (cell (237+t)) (h t) p) ∧
    (¬ ∃ g : Int → Bool, Subset (cell 255) (cell 236) g ∧
      ∀ p, diffStep (cell 255) (cell 236) g p=h 0 p) := by
  have heq : ∀ t, t ≤ 7 → evolved 256 237 t=field 256 237 t := by
    intro t ht
    exact evolved_eq 256 237 23 6 t gap_256 (by decide) (by decide) ht
  refine ⟨evolved 256 237,field_subset 256 237 (by decide),?_,?_,?_,?_,?_,?_⟩
  · intro p hp
    rcases hp with hp | hp
    · exact field_white_left 256 237 0 (by decide) p (by omega)
    · exact field_white_right 256 237 0 (by decide) p (by omega)
  · intro t ht
    rw [heq t (by omega)]
    exact ⟨field_left 256 237 t (by decide),field_white_left 256 237 t (by decide)⟩
  · intro t ht
    rw [heq t (by omega)]
    exact field_center 256 237 6 t (by decide) ht (center_agreement_6 t ht)
  · intro t ht
    rw [heq t (by omega)]
    exact (field_mode 256 237 23 6 t gap_256 (by decide) (by decide) ht).2
  · intro t p; rfl
  · exact field_nonlift 256 237 23 (by decide) (by decide) (by decide) gap_256 prior_255_at_236

end Rule30SensorClosureResearch
