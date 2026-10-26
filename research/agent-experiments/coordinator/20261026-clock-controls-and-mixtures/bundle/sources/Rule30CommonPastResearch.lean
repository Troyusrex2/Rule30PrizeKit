module
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals

/-! Exact past compatibility in right-edge coordinates. The period argument
extends the official diagonal xor-accumulation lemma to arbitrary rows and
their common linear mode. It recovers all-future local constraints backward.
No finite left support or fixed-center condition is asserted for the lift.
This is not a proof of P1, CQ01 or the canonical observer conjecture. -/
@[expose] public section
namespace Rule30CommonPastResearch
open Ruliology.CellularAutomata
open Rule30Jen (rule)
open Rule30Diagonals (xor_accum_periodic periodic_double)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def march (x : Nat → Bool) : Nat → Bool
  | 0 => x 0
  | 1 => xor (x 1) (x 0)
  | j+2 => xor (x (j+2)) (x (j+1) || x j)

def modeStep (a b h : Nat → Bool) : Nat → Bool
  | 0 => h 0
  | 1 => xor (h 1) (h 0)
  | j+2 => xor (h (j+2)) (xor ((!b j) && h (j+1)) ((!a (j+1)) && h j))

def Actual (a : Nat → Nat → Bool) : Prop := ∀ t j, a (t+1) j=march (a t) j
def Mode (a b h : Nat → Nat → Bool) : Prop :=
  ∀ t j, h (t+1) j=modeStep (a t) (b t) (h t) j
def GoodAt (a b h : Nat → Nat → Bool) (t j : Nat) : Prop :=
  (xor (a t j) (b t j) && h t (j+1))=(h t j && xor (a t (j+1)) (b t (j+1)))
def Common (a b h : Nat → Nat → Bool) : Prop := ∀ t j, GoodAt a b h t j
def SubAt (a b h : Nat → Nat → Bool) (t j : Nat) : Prop :=
  (h t j && xor (a t j) (b t j))=h t j
def Subset (a b h : Nat → Nat → Bool) : Prop := ∀ t j, SubAt a b h t j
def Finite (x : Nat → Bool) : Prop := ∃ N, ∀ j, N≤j → x j=false

theorem raise_period {f : Nat → Bool} (j : Nat)
    (hp : ∀ t, f (t+2^j)=f t) : ∀ t, f (t+2^(j+1))=f t := by
  intro t
  rw [show 2^(j+1)=2*2^j by rw [Nat.pow_succ]; omega]
  exact periodic_double hp t

/-- Arbitrary right-bounded starts, not just the single seed. -/
theorem actual_periodic (a : Nat → Nat → Bool) (ha : Actual a) :
    ∀ j t, a (t+2^j) j=a t j := by
  have pair : ∀ j, (∀ t, a (t+2^j) j=a t j) ∧
      (∀ t, a (t+2^(j+1)) (j+1)=a t (j+1)) := by
    intro j
    induction j with
    | zero =>
      have h0 : ∀ t, a (t+1) 0=a t 0 := fun t => ha t 0
      refine ⟨by simpa using h0, ?_⟩
      have hx : ∀ t, a (t+1) 1=xor (a t 1) (a t 0) := fun t => ha t 1
      have hp := xor_accum_periodic (x:=fun t => a t 1) (g:=fun t => a t 0) (L:=1) hx h0
      simpa using hp
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have hg : ∀ t, (a (t+2^(j+1)) (j+1) || a (t+2^(j+1)) j)=
          (a t (j+1) || a t j) := by
        intro t
        rw [ih.2 t,raise_period (f:=fun s => a s j) j ih.1 t]
      have hx : ∀ t, a (t+1) (j+2)=xor (a t (j+2)) (a t (j+1) || a t j) :=
        fun t => ha t (j+2)
      have hp := xor_accum_periodic (x:=fun t => a t (j+2))
        (g:=fun t => a t (j+1) || a t j) (L:=2^(j+1)) hx hg
      intro t
      rw [show 2^(j+1+1)=2*2^(j+1) by rw [Nat.pow_succ]; omega]
      exact hp t
  exact fun j => (pair j).1

/-- Both coefficient histories evolve physically. No left-support condition. -/
theorem mode_periodic (a b h : Nat → Nat → Bool)
    (ha : Actual a) (hb : Actual b) (hh : Mode a b h) :
    ∀ j t, h (t+2^j) j=h t j := by
  have ap := actual_periodic a ha
  have bp := actual_periodic b hb
  have pair : ∀ j, (∀ t, h (t+2^j) j=h t j) ∧
      (∀ t, h (t+2^(j+1)) (j+1)=h t (j+1)) := by
    intro j
    induction j with
    | zero =>
      have h0 : ∀ t, h (t+1) 0=h t 0 := fun t => hh t 0
      refine ⟨by simpa using h0, ?_⟩
      have hx : ∀ t, h (t+1) 1=xor (h t 1) (h t 0) := fun t => hh t 1
      simpa using xor_accum_periodic (x:=fun t => h t 1) (g:=fun t => h t 0) (L:=1) hx h0
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have hg : ∀ t,
          xor ((!b (t+2^(j+1)) j) && h (t+2^(j+1)) (j+1))
              ((!a (t+2^(j+1)) (j+1)) && h (t+2^(j+1)) j)=
          xor ((!b t j) && h t (j+1)) ((!a t (j+1)) && h t j) := by
        intro t
        rw [raise_period (f:=fun s => b s j) j (bp j) t,ih.2 t,ap (j+1) t,
          raise_period (f:=fun s => h s j) j ih.1 t]
      have hx : ∀ t, h (t+1) (j+2)=xor (h t (j+2))
          (xor ((!b t j) && h t (j+1)) ((!a t (j+1)) && h t j)) :=
        fun t => hh t (j+2)
      have hp := xor_accum_periodic (x:=fun t => h t (j+2))
        (g:=fun t => xor ((!b t j) && h t (j+1)) ((!a t (j+1)) && h t j))
        (L:=2^(j+1)) hx hg
      intro t
      rw [show 2^(j+1+1)=2*2^(j+1) by rw [Nat.pow_succ]; omega]
      exact hp t
  exact fun j => (pair j).1

theorem periodic_prop_retro (P : Nat → Prop) (L T : Nat) (hL : 0<L)
    (hp : ∀ t, P (t+L) ↔ P t) (he : ∀ t, T≤t → P t) : ∀ t, P t := by
  have mult : ∀ n t, P (t+n*L) ↔ P t := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      rw [Nat.succ_mul,show t+(n*L+L)=(t+n*L)+L by omega,hp,ih]
  intro t
  have hmul : T≤T*L := by
    simpa using Nat.mul_le_mul_left T (show 1≤L by omega)
  exact (mult T t).mp (he (t+T*L) (by omega))

theorem common_from_future (a b h : Nat → Nat → Bool)
    (ha : Actual a) (hb : Actual b) (hh : Mode a b h) (T : Nat)
    (hw : ∀ t, T≤t → ∀ j, GoodAt a b h t j) : Common a b h := by
  have ap := actual_periodic a ha
  have bp := actual_periodic b hb
  have hp := mode_periodic a b h ha hb hh
  intro t j
  apply periodic_prop_retro (fun s => GoodAt a b h s j) (2^(j+1)) T
      (by exact Nat.pow_pos (by decide)) ?_ (fun s hs => hw s hs j) t
  intro s
  unfold GoodAt
  rw [raise_period (f:=fun t => a t j) j (ap j) s,
    raise_period (f:=fun t => b t j) j (bp j) s,hp (j+1) s,
    raise_period (f:=fun t => h t j) j (hp j) s,ap (j+1) s,bp (j+1) s]

theorem subset_from_future (a b h : Nat → Nat → Bool)
    (ha : Actual a) (hb : Actual b) (hh : Mode a b h) (T : Nat)
    (hs : ∀ t, T≤t → ∀ j, SubAt a b h t j) : Subset a b h := by
  have ap := actual_periodic a ha
  have bp := actual_periodic b hb
  have hp := mode_periodic a b h ha hb hh
  intro t j
  apply periodic_prop_retro (fun s => SubAt a b h s j) (2^j) T
      (by exact Nat.pow_pos (by decide)) ?_ (fun s ht => hs s ht j) t
  intro s
  unfold SubAt
  rw [hp j s,ap j s,bp j s]

def invStep (a b y : Nat → Bool) : Nat → Bool
  | 0 => y 0
  | 1 => xor (y 1) (invStep a b y 0)
  | j+2 => xor (y (j+2))
      (xor ((!b j) && invStep a b y (j+1)) ((!a (j+1)) && invStep a b y j))

theorem cancel : ∀ x y : Bool, xor (xor x y) y=x := by decide +kernel

theorem step_inv (a b y : Nat → Bool) (j : Nat) :
    modeStep a b (invStep a b y) j=y j := by
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero => exact cancel _ _
    | succ j => exact cancel _ _

theorem inv_step (a b x : Nat → Bool) : ∀ j,
    invStep a b (modeStep a b x) j=x j := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero =>
        change xor (xor (x 1) (x 0)) (invStep a b (modeStep a b x) 0)=x 1
        rw [ih 0 (by omega)]
        exact cancel _ _
      | succ j =>
        change xor (xor (x (j+2)) (xor ((!b j) && x (j+1)) ((!a (j+1)) && x j)))
            (xor ((!b j) && invStep a b (modeStep a b x) (j+1))
              ((!a (j+1)) && invStep a b (modeStep a b x) j))=x (j+2)
        rw [ih (j+1) (by omega),ih j (by omega)]
        exact cancel _ _

theorem step_injective (a b x y : Nat → Bool)
    (he : ∀ j, modeStep a b x j=modeStep a b y j) : ∀ j, x j=y j := by
  intro j
  have hh := congrArg (fun z => invStep a b z j) (funext he)
  simpa only [inv_step] using hh

/-- The unique past lift may have an infinite left tail. -/
theorem common_past_lift (a b H : Nat → Nat → Bool)
    (ha : Actual a) (hb : Actual b)
    (hh : Mode (fun t => a (t+1)) (fun t => b (t+1)) H)
    (hw : Common (fun t => a (t+1)) (fun t => b (t+1)) H) :
    ∃ G, Mode a b G ∧ Common a b G ∧ (∀ t j, G (t+1) j=H t j) ∧
      (∀ G', Mode a b G' → (∀ t j, G' (t+1) j=H t j) → ∀ t j, G' t j=G t j) := by
  let G : Nat → Nat → Bool := fun t => match t with
    | 0 => invStep (a 0) (b 0) (H 0)
    | t+1 => H t
  have hg : Mode a b G := by
    intro t j
    cases t with
    | zero => exact (step_inv (a 0) (b 0) (H 0) j).symm
    | succ t => simpa only [G,Nat.add_assoc] using hh t j
  have hshift : ∀ t j, G (t+1) j=H t j := fun _ _ => rfl
  refine ⟨G,hg,?_,hshift,?_⟩
  · apply common_from_future a b G ha hb hg 1
    intro t ht j
    cases t with
    | zero => omega
    | succ t => exact hw t j
  · intro G' hg' hshift' t j
    cases t with
    | zero =>
      apply step_injective (a 0) (b 0) (G' 0) (G 0) ?_ j
      intro k
      rw [←hg' 0 k,←hg 0 k,hshift' 0 k,hshift 0 k]
    | succ t => exact (hshift' t j).trans (hshift t j).symm

/-- Subset is assumed at every future time; no initial-only variant is proved. -/
theorem common_subset_past_lift (a b H : Nat → Nat → Bool)
    (ha : Actual a) (hb : Actual b)
    (hh : Mode (fun t => a (t+1)) (fun t => b (t+1)) H)
    (hw : Common (fun t => a (t+1)) (fun t => b (t+1)) H)
    (hs : Subset (fun t => a (t+1)) (fun t => b (t+1)) H) :
    ∃ G, Mode a b G ∧ Common a b G ∧ Subset a b G ∧ (∀ t j, G (t+1) j=H t j) := by
  obtain ⟨G,hg,hc,hshift,_⟩ := common_past_lift a b H ha hb hh hw
  refine ⟨G,hg,hc,?_,hshift⟩
  apply subset_from_future a b G ha hb hg 1
  intro t ht j
  cases t with
  | zero => omega
  | succ t =>
    unfold SubAt
    rw [hshift t j]
    exact hs t j

theorem subset_finite (a b h : Nat → Bool) (ha : Finite a) (hb : Finite b)
    (hs : ∀ j, (h j && xor (a j) (b j))=h j) : Finite h := by
  obtain ⟨A,ha⟩ := ha
  obtain ⟨B,hb⟩ := hb
  refine ⟨max A B,fun j hj => ?_⟩
  have he := hs j
  rw [ha j (by omega),hb j (by omega)] at he
  simpa using he.symm

/-- This uses the stated all-future subset premise, not an initial-only variant. -/
theorem finite_common_past_lift (a b H : Nat → Nat → Bool)
    (ha : Actual a) (hb : Actual b) (hfa : Finite (a 0)) (hfb : Finite (b 0))
    (hh : Mode (fun t => a (t+1)) (fun t => b (t+1)) H)
    (hw : Common (fun t => a (t+1)) (fun t => b (t+1)) H)
    (hs : Subset (fun t => a (t+1)) (fun t => b (t+1)) H) :
    ∃ G, Mode a b G ∧ Common a b G ∧ Subset a b G ∧ Finite (G 0) ∧
      (∀ t j, G (t+1) j=H t j) := by
  obtain ⟨G,hg,hc,hsub,hshift⟩ := common_subset_past_lift a b H ha hb hh hw hs
  exact ⟨G,hg,hc,hsub,subset_finite (a 0) (b 0) (G 0) hfa hfb (hsub 0),hshift⟩

theorem recombine_local : ∀ l c r bc br hl hc hr : Bool,
    (hc && xor c bc)=hc → (hr && xor r br)=hr →
    (xor c bc && hr)=(hc && xor r br) →
    rule (xor l hl) (xor c hc) (xor r hr)=
      xor (rule l c r) (xor hl (xor ((!br) && hc) ((!c) && hr))) := by
  decide +kernel

theorem march_recombined (a b h : Nat → Bool)
    (hs : ∀ j, (h j && xor (a j) (b j))=h j)
    (hw : ∀ j, (xor (a j) (b j) && h (j+1))=
      (h j && xor (a (j+1)) (b (j+1)))) (j : Nat) :
    march (fun i => xor (a i) (h i)) j=xor (march a j) (modeStep a b h j) := by
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero =>
      change xor (xor (a 1) (h 1)) (xor (a 0) (h 0))=
        xor (xor (a 1) (a 0)) (xor (h 1) (h 0))
      cases a 1 <;> cases a 0 <;> cases h 1 <;> cases h 0 <;> rfl
    | succ j =>
      have hg : (xor (a (j+1)) (b (j+1)) && h j)=
          (h (j+1) && xor (a j) (b j)) := by
        simpa only [Bool.and_comm] using (hw j).symm
      exact recombine_local (a (j+2)) (a (j+1)) (a j) (b (j+1)) (b j)
        (h (j+2)) (h (j+1)) (h j) (hs (j+1)) (hs j) hg

/-- All-time subset removes the quadratic curvature at every step. -/
theorem actual_recombination (a b h : Nat → Nat → Bool)
    (ha : Actual a) (hh : Mode a b h) (hw : Common a b h) (hs : Subset a b h) :
    Actual (fun t j => xor (a t j) (h t j)) := by
  intro t j
  change xor (a (t+1) j) (h (t+1) j)=march (fun i => xor (a t i) (h t i)) j
  rw [ha t j,hh t j]
  exact (march_recombined (a t) (b t) (h t) (hs t) (hw t) j).symm

/-! A support warning: with vacuum coefficients the unique past of a finite
pulse has an infinite left tail. It violates the subset premise. -/
def tail110 (j : Nat) : Bool := decide (j%3≠2)
def pulse0 (j : Nat) : Bool := decide (j=0)

theorem tail_step (j : Nat) :
    modeStep (fun _ => false) (fun _ => false) tail110 j=pulse0 j := by
  cases j with
  | zero => decide +kernel
  | succ j =>
    cases j with
    | zero => decide +kernel
    | succ j =>
      have hm : j%3=0 ∨ j%3=1 ∨ j%3=2 := by omega
      rcases hm with hm|hm|hm
      all_goals simp [modeStep,tail110,pulse0,Nat.add_mod,hm]

theorem tail_infinite (N : Nat) : ∃ j, N≤j ∧ tail110 j=true := by
  refine ⟨3*N,by omega,?_⟩
  simp [tail110]

theorem vacuum_pulse_no_finite_past :
    ¬ ∃ g, Finite g ∧ ∀ j,
      modeStep (fun _ => false) (fun _ => false) g j=pulse0 j := by
  rintro ⟨g,hfin,hg⟩
  have he : ∀ j, g j=tail110 j :=
    step_injective (fun _ => false) (fun _ => false) g tail110
      (fun j => (hg j).trans (tail_step j).symm)
  obtain ⟨N,hN⟩ := hfin
  obtain ⟨j,hj,ht⟩ := tail_infinite N
  have hz := hN j hj
  rw [he j,ht] at hz
  cases hz

/-! The coordinate model is an exact physical Rule30 model. The wall/march
calculation adapts the earlier finite-rectangle coordinate bridge. -/
def wall (x : Nat → Bool) (n : Int) : Bool := if 0≤n then x n.toNat else false

theorem wall_march (x : Nat → Bool) (n : Int) :
    wall (march x) n=rule (wall x n) (wall x (n-1)) (wall x (n-2)) := by
  by_cases hn : 0≤n
  · have he : n=(n.toNat : Int) := by omega
    rw [he]
    generalize n.toNat=k
    cases k with
    | zero => simp [wall,march,rule]
    | succ k =>
      cases k with
      | zero => simp [wall,march,rule]
      | succ k =>
        simp only [wall,show (0:Int)≤((k+1+1:Nat):Int) by omega,
          show (0:Int)≤((k+1+1:Nat):Int)-1 by omega,
          show (0:Int)≤((k+1+1:Nat):Int)-2 by omega,ite_true,
          show (((k+1+1:Nat):Int)-1).toNat=k+1 by omega,
          show (((k+1+1:Nat):Int)-2).toNat=k by omega,Int.toNat_natCast,march,rule]
  · simp only [wall,hn,show ¬(0:Int)≤n-1 by omega,
      show ¬(0:Int)≤n-2 by omega,ite_false,rule]
    rfl

theorem wall_mode (a b h : Nat → Bool) (n : Int) :
    wall (modeStep a b h) n=xor (wall h n)
      (xor ((!wall b (n-2)) && wall h (n-1)) ((!wall a (n-1)) && wall h (n-2))) := by
  by_cases hn : 0≤n
  · have he : n=(n.toNat : Int) := by omega
    rw [he]
    generalize n.toNat=k
    cases k with
    | zero => simp [wall,modeStep]
    | succ k =>
      cases k with
      | zero => simp [wall,modeStep]
      | succ k =>
        simp only [wall,show (0:Int)≤((k+1+1:Nat):Int) by omega,
          show (0:Int)≤((k+1+1:Nat):Int)-1 by omega,
          show (0:Int)≤((k+1+1:Nat):Int)-2 by omega,ite_true,
          show (((k+1+1:Nat):Int)-1).toNat=k+1 by omega,
          show (((k+1+1:Nat):Int)-2).toNat=k by omega,Int.toNat_natCast,modeStep]
  · simp only [wall,hn,show ¬(0:Int)≤n-1 by omega,
      show ¬(0:Int)≤n-2 by omega,ite_false]
    rfl

def physical (x : Nat → Nat → Bool) (t : Nat) (p : Int) : Bool :=
  wall (x t) ((t:Int)-p)

theorem physical_actual (a : Nat → Nat → Bool) (ha : Actual a) (t : Nat) (p : Int) :
    physical a (t+1) p=rule (physical a t (p-1)) (physical a t p) (physical a t (p+1)) := by
  unfold physical
  rw [show a (t+1)=march (a t) by funext j;exact ha t j,wall_march]
  congr 1 <;> congr 1 <;> omega

theorem physical_mode (a b h : Nat → Nat → Bool) (hh : Mode a b h) (t : Nat) (p : Int) :
    physical h (t+1) p=xor (physical h t (p-1))
      (xor ((!physical b t (p+1)) && physical h t p)
        ((!physical a t p) && physical h t (p+1))) := by
  unfold physical
  rw [show h (t+1)=modeStep (a t) (b t) (h t) by funext j;exact hh t j,wall_mode]
  rw [show (((t+1:Nat):Int)-p)-2=(t:Int)-(p+1) by omega,
    show (((t+1:Nat):Int)-p)-1=(t:Int)-p by omega,
    show ((t+1:Nat):Int)-p=(t:Int)-(p-1) by omega]

end Rule30CommonPastResearch
