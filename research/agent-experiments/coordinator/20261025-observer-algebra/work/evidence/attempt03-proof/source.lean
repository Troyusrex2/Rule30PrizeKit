module

public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
An auxiliary observer warning, not a solution of Problem 1.
The backgrounds below are infinite periodic rows at time zero. They merge
after one step and become vacuum after two. The finite auxiliary modes are
invisible for every time and every divided-difference gauge. In particular,
eventual vacuum and gauge identities alone do not restore physicality.
No counterexample for finite or left-bounded initial backgrounds is claimed.
-/

@[expose] public section
namespace Rule30ObserverBarrierResearch
open Ruliology.CellularAutomata Rule30Jen Rule30Realization

def A (p : Int) : Bool := decide (p % 3 = 1)
def B (p : Int) : Bool := decide (p % 3 = 2)

def mix (c r l x y : Bool) : Bool := xor (xor l (c && x)) (r && y)

theorem mix_add : ∀ c r l x y l' x' y' : Bool,
    mix c r (xor l l') (xor x x') (xor y y') =
      xor (mix c r l x y) (mix c r l' x' y') := by decide +kernel

theorem curvature : ∀ a b c d e f l x y : Bool,
    xor (xor (rule (xor a l) (xor b x) (xor c y)) (rule a b c))
      (mix (!f) (!b) l x y) = (x && xor (xor c f) y) := by decide +kernel

theorem phase_periodic (n p : Int) : A (p-3*n)=A p ∧ B (p-3*n)=B p := by
  unfold A B
  have hm : (p-3*n)%3=p%3 := by omega
  simp only [hm]
  exact ⟨rfl,rfl⟩

theorem backgrounds_one (p : Int) : evol A 1 p=true ∧ evol B 1 p=true := by
  have hm : p%3=0 ∨ p%3=1 ∨ p%3=2 := by omega
  rcases hm with hm|hm|hm <;>
    simp [evol,A,B,rule,show (p-1)%3=(p%3+2)%3 by omega,
      show (p+1)%3=(p%3+1)%3 by omega,hm]

theorem backgrounds_vacuum : ∀ (t : Nat) (p : Int),
    evol A (t+2) p=false ∧ evol B (t+2) p=false
  | 0,p => by
      change rule (evol A 1 (p-1)) (evol A 1 p) (evol A 1 (p+1))=false ∧
        rule (evol B 1 (p-1)) (evol B 1 p) (evol B 1 (p+1))=false
      rw [(backgrounds_one _).1,(backgrounds_one _).1,(backgrounds_one _).1,
        (backgrounds_one _).2,(backgrounds_one _).2,(backgrounds_one _).2]
      exact ⟨rfl,rfl⟩
  | t+1,p => by
      change rule (evol A (t+2) (p-1)) (evol A (t+2) p) (evol A (t+2) (p+1))=false ∧
        rule (evol B (t+2) (p-1)) (evol B (t+2) p) (evol B (t+2) (p+1))=false
      rw [(backgrounds_vacuum t _).1,(backgrounds_vacuum t _).1,(backgrounds_vacuum t _).1,
        (backgrounds_vacuum t _).2,(backgrounds_vacuum t _).2,(backgrounds_vacuum t _).2]
      exact ⟨rfl,rfl⟩

def lin (t : Nat) (h : Int → Bool) (p : Int) : Bool :=
  mix (!(evol B t (p+1))) (!(evol A t p)) (h (p-1)) (h p) (h (p+1))

theorem lin_add (t : Nat) (h g : Int → Bool) (p : Int) :
    lin t (fun q => xor (h q) (g q)) p=xor (lin t h p) (lin t g p) :=
  mix_add _ _ _ _ _ _ _ _

def shifted (d : Int) (h : Int → Bool) (p : Int) : Bool := h (p-d)
def run0 (p : Int) : Bool := decide (p=1 ∨ p=2)
def image0 (p : Int) : Bool := decide (p=0 ∨ p=3)
def run (n : Int) := shifted (3*n) run0
def image (n : Int) := shifted (3*n) image0

theorem run0_step (p : Int) : lin 0 run0 p=image0 p := by
  by_cases hp : 0≤p ∧ p≤3
  · obtain rfl|rfl|rfl|rfl : p=0 ∨ p=1 ∨ p=2 ∨ p=3 := by omega
    all_goals decide +kernel
  · have h0 : p≠0 := by omega
    have h3 : p≠3 := by omega
    have hleft : p-1≠1 ∧ p-1≠2 := by omega
    have hcenter : p≠1 ∧ p≠2 := by omega
    have hright : p+1≠1 ∧ p+1≠2 := by omega
    simp [lin,mix,run0,image0,h0,h3,hleft,hcenter,hright]

theorem lin_shift (n : Int) (h : Int → Bool) (p : Int) :
    lin 0 (shifted (3*n) h) p=shifted (3*n) (lin 0 h) p := by
  simp only [lin,shifted,evol]
  rw [(phase_periodic n (p+1)).2,(phase_periodic n p).1]
  rw [show p-3*n+1=(p+1)-3*n by omega,
      show p-1-3*n=p-3*n-1 by omega]

theorem run_step (n p : Int) : lin 0 (run n) p=image n p := by
  rw [run,lin_shift]
  exact run0_step (p-3*n)

theorem run_wedge (n p : Int) :
    xor (xor (A (p+1)) (B (p+1)) && run n p)
      (xor (A p) (B p) && run n (p+1))=false := by
  by_cases hp : 3*n≤p ∧ p≤3*n+2
  · obtain rfl|rfl|rfl : p=3*n ∨ p=3*n+1 ∨ p=3*n+2 := by omega
    all_goals
      norm_num [run,shifted,run0,A,B,Int.add_emod,Int.mul_emod]
  · have hp0 : p-3*n≠1 ∧ p-3*n≠2 := by omega
    have hp1 : (p+1)-3*n≠1 ∧ (p+1)-3*n≠2 := by omega
    simp [run,shifted,run0,hp0,hp1]

def h0 (k : Int) (p : Int) := xor (run (-k-1) p) (run k p)
def h1 (k : Int) (p : Int) := xor (image (-k-1) p) (image k p)
def h2 (k : Int) (p : Int) := h1 k (p-1)

def addEvol (x : Int → Bool) : Nat → Int → Bool
  | 0,p => x p
  | t+1,p => xor (xor (addEvol x t (p-1)) (addEvol x t p)) (addEvol x t (p+1))

theorem add_reflect {x : Int → Bool} (hx : ∀ p, x (2-p)=x p) :
    ∀ (t : Nat) (p : Int), addEvol x t (2-p)=addEvol x t p
  | 0,p => hx p
  | t+1,p => by
      simp only [addEvol,show 2-p-1=2-(p+1) by omega,
        show 2-p+1=2-(p-1) by omega,add_reflect hx t]
      cases addEvol x t (p-1) <;> cases addEvol x t p <;>
        cases addEvol x t (p+1) <;> rfl

theorem add_center {x : Int → Bool} (hx : ∀ p, x (2-p)=x p) (hcenter : x 1=false) :
    ∀ t, addEvol x t 1=false
  | 0 => hcenter
  | t+1 => by
      have hs := add_reflect hx t 0
      change addEvol x t 2=addEvol x t 0 at hs
      simp only [addEvol,show (1:Int)-1=0 by omega,show (1:Int)+1=2 by omega,
        add_center hx hcenter t,hs]
      cases addEvol x t 0 <;> rfl

theorem image_reflect (n p : Int) : image (-n-1) (-p)=image n p := by
  have h0 : -p-3*(-n-1)=0 ↔ p-3*n=3 := by omega
  have h3 : -p-3*(-n-1)=3 ↔ p-3*n=0 := by omega
  simp only [image,shifted,image0,h0,h3,or_comm]

theorem h1_reflect (k p : Int) : h1 k (-p)=h1 k p := by
  have hl := image_reflect k p
  have hr := image_reflect (-k-1) p
  rw [show -(-k-1)-1=k by omega] at hr
  simp only [h1,hl,hr,Bool.xor_comm]

theorem h2_reflect (k p : Int) : h2 k (2-p)=h2 k p := by
  unfold h2
  rw [show 2-p-1=-(p-1) by omega,h1_reflect]

theorem h2_center (k : Int) (hk : 1≤k) : h2 k 1=false := by
  have h0 : 0-3*(-k-1)≠0 ∧ 0-3*(-k-1)≠3 := by omega
  have h1 : 0-3*k≠0 ∧ 0-3*k≠3 := by omega
  simp [h2,Rule30ObserverBarrierResearch.h1,image,shifted,image0,h0,h1]

def H (k : Int) : Nat → Int → Bool
  | 0 => h0 k
  | 1 => h1 k
  | t+2 => addEvol (h2 k) t

theorem H_step (k : Int) : ∀ (t : Nat) (p : Int), H k (t+1) p=lin t (H k t) p
  | 0,p => by simp only [H,h0,h1,lin_add,run_step]
  | 1,p => by
      simp only [H,lin,(backgrounds_one _).1,(backgrounds_one _).2,
        Bool.not_true,Bool.false_and,mix,Bool.xor_false,addEvol,h2]
  | t+2,p => by
      simp only [H,lin,(backgrounds_vacuum t _).1,(backgrounds_vacuum t _).2,
        Bool.not_false,Bool.true_and,mix,addEvol]

theorem H_center (k : Int) (hk : 1≤k) : ∀ t, H k t 1=false
  | 0 => by
      have hl : 1-3*(-k-1)≠1 ∧ 1-3*(-k-1)≠2 := by omega
      have hr : 1-3*k≠1 ∧ 1-3*k≠2 := by omega
      simp [H,h0,run,shifted,run0,hl,hr]
  | 1 => by
      have hl : 1-3*(-k-1)≠0 ∧ 1-3*(-k-1)≠3 := by omega
      have hr : 1-3*k≠0 ∧ 1-3*k≠3 := by omega
      simp [H,h1,image,shifted,image0,hl,hr]
  | t+2 => add_center (h2_reflect k) (h2_center k hk) t

def delta (t : Nat) (p : Int) := xor (evol A t p) (evol B t p)
def wedge (t : Nat) (h : Int → Bool) (p : Int) :=
  xor (delta t (p+1) && h p) (delta t p && h (p+1))

theorem wedge_add : ∀ a b x y x' y' : Bool,
    xor (a && xor x x') (b && xor y y') =
      xor (xor (a && x) (b && y)) (xor (a && x') (b && y')) := by decide +kernel

theorem H_wedge (k : Int) : ∀ (t : Nat) (p : Int), wedge t (H k t) p=false
  | 0,p => by
      simp only [wedge,delta,evol,H,h0,wedge_add,run_wedge,Bool.false_xor]
  | 1,p => by
      simp [wedge,delta,(backgrounds_one _).1,(backgrounds_one _).2]
  | t+2,p => by
      simp [wedge,delta,(backgrounds_vacuum t _).1,(backgrounds_vacuum t _).2]

def gauged (g : Nat → Int → Bool) (t : Nat) (h : Int → Bool) (p : Int) :=
  mix (xor (!(evol B t (p+1))) (g t p && delta t (p+1)))
      (xor (!(evol A t p)) (g t p && delta t p)) (h (p-1)) (h p) (h (p+1))

theorem gauge_identity : ∀ c r g a b l x y : Bool,
    mix (xor c (g && a)) (xor r (g && b)) l x y =
      xor (mix c r l x y) (g && xor (a && x) (b && y)) := by decide +kernel

theorem H_any_gauge (g : Nat → Int → Bool) (k : Int) (t : Nat) (p : Int) :
    gauged g t (H k t) p=H k (t+1) p := by
  rw [gauged,gauge_identity]
  change xor (lin t (H k t) p) (g t p && wedge t (H k t) p)=_
  rw [H_wedge,Bool.and_false,Bool.xor_false,H_step]

def gaugeEvol (g : Nat → Int → Bool) (x : Int → Bool) : Nat → Int → Bool
  | 0,p => x p
  | t+1,p => gauged g t (gaugeEvol g x t) p

theorem gaugeEvol_eq (g : Nat → Int → Bool) (k : Int) :
    ∀ t, gaugeEvol g (h0 k) t=H k t
  | 0 => rfl
  | t+1 => by
      funext p
      simp only [gaugeEvol,gaugeEvol_eq g k t,H_any_gauge]

theorem finite_mode (k : Int) (hk : 1≤k) : Rule30PeriodTwoSideways.FinConfig (h0 k) := by
  refine ⟨(3*k+2).toNat,?_⟩
  intro p hp
  have hl : p-3*(-k-1)≠1 ∧ p-3*(-k-1)≠2 := by omega
  have hr : p-3*k≠1 ∧ p-3*k≠2 := by omega
  simp [h0,run,shifted,run0,hl,hr]

theorem source_bit (k : Int) (hk : 1≤k) :
    h0 k (-3*k-2)=true ∧ A (-3*k-2)=true ∧ B (-3*k-2)=false := by
  have hm : (-3*k-2)%3=1 := by omega
  have hl : -3*k-2-3*(-k-1)=1 := by omega
  have hr : -3*k-2-3*k≠1 ∧ -3*k-2-3*k≠2 := by omega
  simp [h0,run,shifted,run0,A,B,hm,hl,hr]

/-- Uniform in the source separation, all times and every local gauge.
The backgrounds are infinite initially. This does not refute the proposed
observer condition for canonical finite starts or prove a prize result. -/
theorem unobservable (g : Nat → Int → Bool) (k : Int) (hk : 1≤k) :
    Rule30PeriodTwoSideways.FinConfig (h0 k) ∧ h0 k (-3*k-2)=true ∧
      ∀ t, gaugeEvol g (h0 k) t 1=false := by
  refine ⟨finite_mode k hk,(source_bit k hk).1,?_⟩
  intro t
  rw [gaugeEvol_eq]
  exact H_center k hk t

theorem recombination_is_not_physical :
    evol (fun p => xor (A p) (h0 1 p)) 4 (-5) ≠ xor (evol A 4 (-5)) (H 1 4 (-5)) := by
  decide +kernel

theorem actual_center_diverges :
    evol (fun p => xor (A p) (h0 1 p)) 7 1=true ∧ H 1 7 1=false := by
  decide +kernel

end Rule30ObserverBarrierResearch
