import Ruliology.CellularAutomata.Rule30Ether
import Ruliology.CellularAutomata.Rule30Realization
import Ruliology.CellularAutomata.Rule30ZeroBoundary
import Ruliology.CellularAutomata.Rule30FiniteConfigs

open Ruliology.CellularAutomata

/-!
# Controlled responses and the triangular right-edge update

The response tree for every possible left driver is equivalent to alternating
head/OR observations of a triangular update. This is an exact controlled-system
equivalence. A single prescribed driver is a different question; no prize
problem is solved here.
-/



namespace Rule30Submission.Response

open Rule30Jen Rule30Ether

abbrev State := Nat → Bool

def prepend (a : Bool) (x : State) : State
  | 0 => a
  | k+1 => x k

def diagonal (x : State) (k : Nat) : Bool :=
  xor (x k) (x (k+1) || x (k+2))

def step (b : Bool) (x : State) : State :=
  prepend (xor b (x 0 || x 1)) (diagonal x)

def run (c : Nat → Bool) (x : State) : Nat → State
  | 0 => x
  | t+1 => step (c t) (run c x t)

def asRight (x : State) (p : Nat) : Bool :=
  if p=0 then false else x (p-1)

/-- The controlled state uses zero-based indexing of the kit's positions 1,2,... . -/
theorem run_sound (c : Nat → Bool) (x : State) : ∀ t k,
    run c x t k=drv c (asRight x) t (k+1) := by
  intro t
  induction t with
  | zero => intro k; simp [run,drv,asRight]
  | succ t ih =>
      intro k
      cases k with
      | zero => simp [run,step,prepend,drv,rule,ih,drv_col0]
      | succ k => simp [run,step,prepend,diagonal,drv,rule,ih,Nat.add_assoc]

theorem run_shift (c : Nat → Bool) (x : State) : ∀ n,
    run c x (n+1)=run (fun j => c (j+1)) (step (c 0) x) n
  | 0 => rfl
  | n+1 => by
      rw [run,run_shift c x n]
      rfl

def ResponseEq : Nat → State → State → Prop
  | 0,_,_ => True
  | n+1,x,y => x 0=y 0 ∧ ∀ b, ResponseEq n (step b x) (step b y)

theorem responseEq_iff_runs (n : Nat) (x y : State) :
    ResponseEq n x y ↔ ∀ c t, t<n → run c x t 0=run c y t 0 := by
  induction n generalizing x y with
  | zero => simp [ResponseEq]
  | succ n ih =>
      constructor
      · intro h c t ht
        cases t with
        | zero => exact h.1
        | succ t =>
            rw [run_shift,run_shift]
            exact (ih (step (c 0) x) (step (c 0) y)).mp (h.2 (c 0)) _ t (by omega)
      · intro h
        refine ⟨h (fun _ => false) 0 (by omega),fun b => ?_⟩
        apply (ih _ _).mpr
        intro c t ht
        have he := h (prepend b c) (t+1) (by omega)
        rw [run_shift,run_shift] at he
        simpa only [prepend] using he

theorem diagonal_prepend (a : Bool) (x : State) : diagonal (prepend a x)=step a x := by
  funext k
  cases k <;> rfl

theorem step_prepend (b a : Bool) (x : State) :
    step b (prepend a x)=prepend (xor b (a || x 0)) (step a x) := by
  unfold step
  rw [diagonal_prepend]
  rfl

private theorem xor_cancel (a b : Bool) : xor (xor a b) b=a := by
  cases a <;> cases b <;> rfl

/-- One arbitrary shared prefix cell costs one observation of the tail system. -/
theorem responseEq_all_prepend (n : Nat) (x y : State) :
    (∀ a, ResponseEq (n+1) (prepend a x) (prepend a y)) ↔ ResponseEq n x y := by
  induction n generalizing x y with
  | zero => simp [ResponseEq,prepend]
  | succ n ih =>
      constructor
      · intro h
        have hhead : x 0=y 0 := by
          have he := ((h false).2 false).1
          simpa [step,prepend] using he
        refine ⟨hhead,fun b => ?_⟩
        apply (ih _ _).mp
        intro a
        have he := (h b).2 (xor a (b || x 0))
        rw [step_prepend,step_prepend,← hhead,xor_cancel] at he
        exact he
      · intro h a
        refine ⟨rfl,fun b => ?_⟩
        rw [step_prepend,step_prepend,h.1]
        exact (ih _ _).mpr (h.2 a) (xor b (a || y 0))

/-- Two observations remove one triangular diagonal layer exactly. -/
theorem responseEq_two (n : Nat) (x y : State) :
    ResponseEq (n+2) x y ↔ x 0=y 0 ∧ (x 0 || x 1)=(y 0 || y 1) ∧
      ResponseEq n (diagonal x) (diagonal y) := by
  constructor
  · intro h
    have hor : (x 0 || x 1)=(y 0 || y 1) := by
      have he := (h.2 false).1
      simpa [step,prepend] using he
    refine ⟨h.1,hor,(responseEq_all_prepend n _ _).mp (fun a => ?_)⟩
    have he := h.2 (xor a (x 0 || x 1))
    change ResponseEq (n+1)
      (prepend (xor (xor a (x 0 || x 1)) (x 0 || x 1)) (diagonal x))
      (prepend (xor (xor a (x 0 || x 1)) (y 0 || y 1)) (diagonal y)) at he
    rw [← hor,xor_cancel] at he
    exact he
  · rintro ⟨hhead,hor,hdiag⟩
    refine ⟨hhead,fun b => ?_⟩
    change ResponseEq (n+1) (prepend (xor b (x 0 || x 1)) (diagonal x))
      (prepend (xor b (y 0 || y 1)) (diagonal y))
    rw [hor]
    exact (responseEq_all_prepend n _ _).mpr hdiag _

def iterate (x : State) : Nat → State
  | 0 => x
  | n+1 => diagonal (iterate x n)

theorem iterate_from (x : State) : ∀ n, iterate (diagonal x) n=iterate x (n+1)
  | 0 => rfl
  | n+1 => by rw [iterate,iterate_from x n]; rfl

def ObserveEq (x y : State) : Prop :=
  x 0=y 0 ∧ (x 0 || x 1)=(y 0 || y 1)

def SameResponse (x y : State) : Prop := ∀ n, ResponseEq n x y

theorem sameResponse_shift {x y : State} (h : SameResponse x y) :
    SameResponse (diagonal x) (diagonal y) :=
  fun n => ((responseEq_two n x y).mp (h (n+2))).2.2

theorem sameResponse_observe {x y : State} (h : SameResponse x y) : ObserveEq x y :=
  ⟨((responseEq_two 0 x y).mp (h 2)).1,((responseEq_two 0 x y).mp (h 2)).2.1⟩

private theorem response_of_diagonal : ∀ n (x y : State),
    (∀ k, ObserveEq (iterate x k) (iterate y k)) → ResponseEq n x y
  | 0,_,_,_ => True.intro
  | 1,x,y,h => ⟨(h 0).1,fun _ => True.intro⟩
  | n+2,x,y,h => (responseEq_two n x y).mpr ⟨(h 0).1,(h 0).2,
      response_of_diagonal n (diagonal x) (diagonal y) (fun k => by
        rw [iterate_from,iterate_from]
        exact h (k+1))⟩

/-- Exact equivalence for every boundary word and observation horizon. -/
theorem sameResponse_iff_diagonal (x y : State) :
    SameResponse x y ↔ ∀ k, ObserveEq (iterate x k) (iterate y k) := by
  constructor
  · intro h
    have hi : ∀ k, SameResponse (iterate x k) (iterate y k) := by
      intro k
      induction k with
      | zero => exact h
      | succ k ih => exact sameResponse_shift ih
    exact fun k => sameResponse_observe (hi k)
  · intro h n
    exact response_of_diagonal n x y h

theorem sameResponse_iff_drv (x y : State) :
    SameResponse x y ↔ ∀ c t, drv c (asRight x) t 1=drv c (asRight y) t 1 := by
  constructor
  · intro h c t
    rw [← run_sound c x t 0,← run_sound c y t 0]
    exact (responseEq_iff_runs (t+1) x y).mp (h _) c t (by omega)
  · intro h n
    apply (responseEq_iff_runs n x y).mpr
    intro c t _
    rw [run_sound,run_sound]
    exact h c t

theorem sameResponse_refl (x : State) : SameResponse x x :=
  (sameResponse_iff_drv x x).mpr (fun _ _ => rfl)

theorem sameResponse_symm {x y : State} (h : SameResponse x y) : SameResponse y x :=
  (sameResponse_iff_drv y x).mpr (fun c t => ((sameResponse_iff_drv x y).mp h c t).symm)

theorem sameResponse_trans {x y z : State} (h : SameResponse x y) (g : SameResponse y z) :
    SameResponse x z :=
  (sameResponse_iff_drv x z).mpr (fun c t =>
    ((sameResponse_iff_drv x y).mp h c t).trans ((sameResponse_iff_drv y z).mp g c t))

theorem sameResponse_prepend {x y : State} (h : SameResponse x y) (a : Bool) :
    SameResponse (prepend a x) (prepend a y) := by
  intro n
  cases n with
  | zero => exact True.intro
  | succ n => exact (responseEq_all_prepend n x y).mpr (h n) a

def withPrefix : List Bool → State → State
  | [],x => x
  | a::bs,x => prepend a (withPrefix bs x)

theorem sameResponse_withPrefix {x y : State} (h : SameResponse x y) (bs : List Bool) :
    SameResponse (withPrefix bs x) (withPrefix bs y) := by
  induction bs with
  | nil => exact h
  | cons a bs ih => exact sameResponse_prepend ih a

def word (bs : List Bool) (k : Nat) : Bool := bs.getD k false

theorem word_cons (a : Bool) (bs : List Bool) : word (a::bs)=prepend a (word bs) := by
  funext k
  cases k <;> rfl

theorem word_append (bs cs : List Bool) : word (bs++cs)=withPrefix bs (word cs) := by
  induction bs with
  | nil => rfl
  | cons a bs ih =>
      rw [List.cons_append,word_cons,withPrefix,ih]

theorem diagonal_011 : diagonal (word [false,true,true])=word [true,false,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
      cases k with
      | zero => rfl
      | succ k => cases k <;> rfl

theorem diagonal_01 : diagonal (word [false,true])=word [true,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

theorem diagonal_101 : diagonal (word [true,false,true])=word [false,true,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
      cases k with
      | zero => rfl
      | succ k => cases k <;> rfl

theorem diagonal_11 : diagonal (word [true,true])=word [false,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

private theorem primitive_responses : ∀ n,
    ResponseEq n (word [false,true,true]) (word [false,true]) ∧
    ResponseEq n (word [true,false,true]) (word [true,true])
  | 0 => ⟨True.intro,True.intro⟩
  | 1 => ⟨⟨rfl,fun _ => True.intro⟩,⟨rfl,fun _ => True.intro⟩⟩
  | n+2 => by
      constructor
      · apply (responseEq_two n _ _).mpr
        refine ⟨rfl,rfl,?_⟩
        rw [diagonal_011,diagonal_01]
        exact (primitive_responses n).2
      · apply (responseEq_two n _ _).mpr
        refine ⟨rfl,rfl,?_⟩
        rw [diagonal_101,diagonal_11]
        exact (primitive_responses n).1

/-- A terminal 011 may be replaced by 01, behind any finite shared prefix. -/
theorem tail_011_response (bs : List Bool) :
    SameResponse (word (bs++[false,true,true])) (word (bs++[false,true])) := by
  rw [word_append,word_append]
  exact sameResponse_withPrefix (fun n => (primitive_responses n).1) bs

/-- A terminal 101 may be replaced by 11, behind any finite shared prefix. -/
theorem tail_101_response (bs : List Bool) :
    SameResponse (word (bs++[true,false,true])) (word (bs++[true,true])) := by
  rw [word_append,word_append]
  exact sameResponse_withPrefix (fun n => (primitive_responses n).2) bs

theorem tail_011_drv (bs : List Bool) (c : Nat → Bool) (t : Nat) :
    drv c (asRight (word (bs++[false,true,true]))) t 1=
      drv c (asRight (word (bs++[false,true]))) t 1 :=
  (sameResponse_iff_drv _ _).mp (tail_011_response bs) c t

theorem tail_101_drv (bs : List Bool) (c : Nat → Bool) (t : Nat) :
    drv c (asRight (word (bs++[true,false,true]))) t 1=
      drv c (asRight (word (bs++[true,true]))) t 1 :=
  (sameResponse_iff_drv _ _).mp (tail_101_response bs) c t

/-- An equivalent finite test without branching over all boundary words. -/
def ObservationPrefix : Nat → State → State → Prop
  | 0,_,_ => True
  | 1,x,y => x 0=y 0
  | n+2,x,y => ObserveEq x y ∧ ObservationPrefix n (diagonal x) (diagonal y)

theorem responseEq_iff_observationPrefix : ∀ n (x y : State),
    ResponseEq n x y ↔ ObservationPrefix n x y
  | 0,_,_ => Iff.rfl
  | 1,_,_ => by simp [ResponseEq,ObservationPrefix]
  | n+2,x,y => by
      rw [responseEq_two,ObservationPrefix,← responseEq_iff_observationPrefix n]
      exact and_assoc.symm

instance observeEqDecidable (x y : State) : Decidable (ObserveEq x y) :=
  inferInstanceAs (Decidable (x 0=y 0 ∧ (x 0 || x 1)=(y 0 || y 1)))

instance observationPrefixDecidable : ∀ n (x y : State), Decidable (ObservationPrefix n x y)
  | 0,_,_ => isTrue True.intro
  | 1,x,y => inferInstanceAs (Decidable (x 0=y 0))
  | n+2,x,y => @instDecidableAnd (ObserveEq x y)
      (ObservationPrefix n (diagonal x) (diagonal y)) (observeEqDecidable x y)
      (observationPrefixDecidable n (diagonal x) (diagonal y))

def shortWindowA : State := word [false,true,false,true,false,true]
def shortWindowB : State := word [false,true,true,false,false,false,true]

/-- Width seven does not make thirteen observations a complete test. -/
theorem short_window_agreement : ResponseEq 13 shortWindowA shortWindowB := by
  rw [responseEq_iff_observationPrefix]
  decide

theorem short_window_not_sameResponse : ¬ SameResponse shortWindowA shortWindowB := by
  intro h
  have he := (sameResponse_iff_diagonal _ _).mp h 8
  have hn : ¬ ObserveEq (iterate shortWindowA 8) (iterate shortWindowB 8) := by decide
  exact hn he

theorem zero_driver_head (x : State) (hx : x 0=true) :
    ∀ t, run (fun _ => false) x t 0=true := by
  intro t
  induction t with
  | zero => exact hx
  | succ t ih => simp [run,step,prepend,ih]

/-- Agreement for one periodic driver does not imply universal response equality.
This externally imposed driver is not asserted to extend to a finite full row. -/
theorem fixed_driver_counterexample :
    (∀ t, drv (fun _ => false) (asRight (word [true])) t 1=
      drv (fun _ => false) (asRight (word [true,true])) t 1) ∧
    ¬ SameResponse (word [true]) (word [true,true]) := by
  constructor
  · intro t
    rw [← run_sound _ _ t 0,← run_sound _ _ t 0]
    rw [zero_driver_head _ rfl,zero_driver_head _ rfl]
  · intro h
    have he := (sameResponse_iff_diagonal _ _).mp h 1
    have hn : ¬ ObserveEq (iterate (word [true]) 1) (iterate (word [true,true]) 1) := by decide
    exact hn he

theorem sameResponse_step {x y : State} (h : SameResponse x y) (b : Bool) :
    SameResponse (step b x) (step b y) := fun n => (h (n+1)).2 b

open Rule30Realization

def rightPart (x : Int → Bool) (k : Nat) : Bool := x ((k:Int)+1)

theorem rightPart_next (x : Int → Bool) (t : Nat) :
    rightPart (evol x (t+1))=step (evol x t 0) (rightPart (evol x t)) := by
  funext k
  cases k with
  | zero => simp [rightPart,evol,step,prepend,rule]
  | succ k =>
      simp [rightPart,evol,step,prepend,diagonal,rule,Int.natCast_add,Int.add_assoc]
      congr 1 <;> omega

/-- Universal right-response equivalence remains sound under actual left feedback. -/
theorem feedback_left_equal {x y : Int → Bool}
    (hleft : ∀ p, p≤0 → x p=y p) (hright : SameResponse (rightPart x) (rightPart y)) :
    ∀ t, (∀ p, p≤0 → evol x t p=evol y t p) ∧
      SameResponse (rightPart (evol x t)) (rightPart (evol y t)) := by
  intro t
  induction t with
  | zero => exact ⟨hleft,hright⟩
  | succ t ih =>
      constructor
      · intro p hp
        have hhead : evol x t 1=evol y t 1 := (sameResponse_observe ih.2).1
        change rule (evol x t (p-1)) (evol x t p) (evol x t (p+1)) =
          rule (evol y t (p-1)) (evol y t p) (evol y t (p+1))
        rw [ih.1 (p-1) (by omega),ih.1 p hp]
        by_cases hz : p=0
        · subst p; rw [show (0:Int)+1=1 by omega,hhead]
        · rw [ih.1 (p+1) (by omega)]
      · rw [rightPart_next,rightPart_next,ih.1 0 (by omega)]
        exact sameResponse_step ih.2 _

def splice (left : Int → Bool) (right : State) (p : Int) : Bool :=
  if p≤0 then left p else right (p.toNat-1)

theorem rightPart_splice (left : Int → Bool) (right : State) :
    rightPart (splice left right)=right := by
  funext k
  simp [rightPart,splice,show ¬ (k:Int)+1≤0 by omega]

theorem splice_same_center (left : Int → Bool) {x y : State} (h : SameResponse x y) (t : Nat) :
    evol (splice left x) t 0=evol (splice left y) t 0 := by
  apply (feedback_left_equal (x:=splice left x) (y:=splice left y) ?_ ?_ t).1 0 (by omega)
  · intro p hp
    simp [splice,hp]
  · rwa [rightPart_splice,rightPart_splice]

theorem tail_011_center (left : Int → Bool) (bs : List Bool) (t : Nat) :
    evol (splice left (word (bs++[false,true,true]))) t 0=
      evol (splice left (word (bs++[false,true]))) t 0 :=
  splice_same_center left (tail_011_response bs) t

theorem tail_101_center (left : Int → Bool) (bs : List Bool) (t : Nat) :
    evol (splice left (word (bs++[true,false,true]))) t 0=
      evol (splice left (word (bs++[true,true]))) t 0 :=
  splice_same_center left (tail_101_response bs) t

end Rule30Submission.Response

/-!
# An eight-periodic infinite-tail obstruction to OR-only reconstruction

The two explicit right halves have identical nonconstant head/neighbor OR
observations and different head traces. Both full diagonal orbits have period
dividing eight. A third example has head period two and full-state least
period eight. None is finitely supported: these are not counterexamples
to the finite-tail conjectures and prove no prize result.
-/



namespace Rule30Submission.Profiles

open Rule30Submission.Response

def key (k : Nat) : Nat := if k<4 then k else 4+(k-4)%4
def nextKey (i : Nat) : Nat := if i<7 then i+1 else 4

theorem key_lt (k : Nat) : key k<8 := by
  unfold key
  split <;> omega

theorem key_succ (k : Nat) : key (k+1)=nextKey (key k) := by
  unfold key nextKey
  split <;> split <;> split <;> omega

def profile (which : Bool) (i : Nat) : Nat :=
  (if which then [45,43,186,166,101,149,86,89]
   else [42,45,51,170,170,85,170,85]).getD i 0

def frame (which : Bool) (t k : Nat) : Bool := (profile which (key k)).testBit (t%8)
def initial (which : Bool) : State := frame which 0

theorem profile_step_table : ∀ which : Bool, ∀ t i : Fin 8,
    (profile which i.val).testBit ((t.val+1)%8)=
      xor ((profile which i.val).testBit t.val)
        ((profile which (nextKey i.val)).testBit t.val ||
         (profile which (nextKey (nextKey i.val))).testBit t.val) := by decide

theorem frame_step (which : Bool) (t : Nat) : diagonal (frame which t)=frame which (t+1) := by
  funext k
  have h := profile_step_table which ⟨t%8,Nat.mod_lt _ (by decide)⟩ ⟨key k,key_lt k⟩
  simpa only [diagonal,frame,key_succ,show k+2=(k+1)+1 by omega,
    show (t+1)%8=(t%8+1)%8 by omega] using h.symm

theorem iterate_frame (which : Bool) : ∀ t, iterate (initial which) t=frame which t
  | 0 => rfl
  | t+1 => by rw [iterate,iterate_frame,frame_step]

theorem full_period_eight (which : Bool) (t : Nat) :
    iterate (initial which) (t+8)=iterate (initial which) t := by
  rw [iterate_frame,iterate_frame]
  funext k
  simp [frame]

theorem same_OR_table : ∀ t : Fin 8,
    ((profile true 0).testBit t.val || (profile true 1).testBit t.val)=
    ((profile false 0).testBit t.val || (profile false 1).testBit t.val) := by decide

theorem same_OR (t : Nat) :
    (iterate (initial true) t 0 || iterate (initial true) t 1)=
    (iterate (initial false) t 0 || iterate (initial false) t 1) := by
  simpa only [iterate_frame,frame,key,show 0<4 by decide,show 1<4 by decide,
    ite_true] using same_OR_table ⟨t%8,Nat.mod_lt _ (by decide)⟩

theorem OR_nonconstant :
    (iterate (initial true) 0 0 || iterate (initial true) 0 1)=true ∧
    (iterate (initial true) 4 0 || iterate (initial true) 4 1)=false := by
  rw [iterate_frame,iterate_frame]
  decide

theorem heads_differ : initial true 0≠initial false 0 := by decide

theorem tail_OR_different :
    (iterate (initial true) 2 1 || iterate (initial true) 2 2)≠
    (iterate (initial false) 2 1 || iterate (initial false) 2 2) := by
  rw [iterate_frame,iterate_frame]
  decide

theorem infinite_true : ¬Rule30ZeroBoundary.FinSupp (initial true) := by
  rintro ⟨W,hW⟩
  have h := hW (4*(W+1)+4) (by omega)
  have hk : key (4*(W+1)+4)=4 := by
    unfold key
    rw [ite_eq_right (by omega)]
    omega
  change (profile true (key (4*(W+1)+4))).testBit 0=false at h
  rw [hk] at h
  contradiction

theorem infinite_false : ¬Rule30ZeroBoundary.FinSupp (initial false) := by
  rintro ⟨W,hW⟩
  have h := hW (4*(W+1)+5) (by omega)
  have hk : key (4*(W+1)+5)=5 := by
    unfold key
    rw [ite_eq_right (by omega)]
    omega
  change (profile false (key (4*(W+1)+5))).testBit 0=false at h
  rw [hk] at h
  contradiction

/-- A third infinite right half: the head has period two but its neighbor
and full diagonal state have least period eight. -/
def lossProfile (i : Nat) : Nat := [85,87,168,212,172,178,202,43].getD i 0
def lossFrame (t k : Nat) : Bool := (lossProfile (key k)).testBit (t%8)
def lossInitial : State := lossFrame 0

theorem loss_step_table : ∀ t i : Fin 8,
    (lossProfile i.val).testBit ((t.val+1)%8)=
      xor ((lossProfile i.val).testBit t.val)
        ((lossProfile (nextKey i.val)).testBit t.val ||
         (lossProfile (nextKey (nextKey i.val))).testBit t.val) := by decide

theorem loss_frame_step (t : Nat) : diagonal (lossFrame t)=lossFrame (t+1) := by
  funext k
  have h := loss_step_table ⟨t%8,Nat.mod_lt _ (by decide)⟩ ⟨key k,key_lt k⟩
  simpa only [diagonal,lossFrame,key_succ,show k+2=(k+1)+1 by omega,
    show (t+1)%8=(t%8+1)%8 by omega] using h.symm

theorem loss_iterate_frame : ∀ t, iterate lossInitial t=lossFrame t
  | 0 => rfl
  | t+1 => by rw [iterate,loss_iterate_frame,loss_frame_step]

theorem loss_full_period_eight (t : Nat) : iterate lossInitial (t+8)=iterate lossInitial t := by
  rw [loss_iterate_frame,loss_iterate_frame]
  funext k
  simp [lossFrame]

theorem loss_head_period_two (t : Nat) : iterate lossInitial (t+2) 0=iterate lossInitial t 0 := by
  have h : ∀ t : Fin 8, (lossProfile 0).testBit ((t.val+2)%8)=(lossProfile 0).testBit t.val := by decide
  simpa only [loss_iterate_frame,lossFrame,key,show 0<4 by decide,ite_true,
    show (t+2)%8=(t%8+2)%8 by omega] using h ⟨t%8,Nat.mod_lt _ (by decide)⟩

theorem loss_neighbor_short_table : ∀ P : Fin 8, 0<P.val → ∃ t : Fin 8,
    (lossProfile 1).testBit ((t.val+P.val)%8)≠(lossProfile 1).testBit t.val := by decide

theorem loss_full_period_lower_bound (P : Nat) (hP : 0<P)
    (hp : ∀ t, iterate lossInitial (t+P)=iterate lossInitial t) : 8≤P := by
  by_cases hbig : 8≤P
  · exact hbig
  · obtain ⟨t,ht⟩ := loss_neighbor_short_table ⟨P,by omega⟩ hP
    have h := congrFun (hp t.val) 1
    simp only [loss_iterate_frame,lossFrame,key,show 1<4 by decide,ite_true,
      Nat.mod_eq_of_lt t.isLt] at h
    exact False.elim (ht h)

theorem loss_not_head_period_one : ¬∀ t, iterate lossInitial (t+1) 0=iterate lossInitial t 0 := by
  intro h
  have hh := h 0
  rw [loss_iterate_frame,loss_iterate_frame] at hh
  contradiction

theorem loss_infinite : ¬Rule30ZeroBoundary.FinSupp lossInitial := by
  rintro ⟨W,hW⟩
  have h := hW (4*(W+1)+7) (by omega)
  have hk : key (4*(W+1)+7)=7 := by
    unfold key
    rw [ite_eq_right (by omega)]
    omega
  change (lossProfile (key (4*(W+1)+7))).testBit 0=false at h
  rw [hk] at h
  contradiction

end Rule30Submission.Profiles

/-!
# Finite feedback can erase a distinction between controlled responses

The right halves `1` and `11` are not universally response equivalent.
When the initial center is white, one actual Rule 30 step sends them to
`11` and `101`, which are universally response equivalent. Consequently
they give the same entire left space-time diagram under any common initial
left half whose center is white. Specializing that left half to white gives
two finite, nonzero configurations with identical, non-eventually-constant
center traces. This does not decide eventual periodicity or distinguish
configurations with different left edges.
-/



namespace Rule30Submission.Feedback

open Rule30Jen Rule30Realization Rule30Submission.Response
open Rule30PeriodTwoSideways Rule30ZeroBoundaryBarriers

theorem step_white_one : step false (word [true]) = word [true,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

theorem step_white_two : step false (word [true,true]) = word [true,false,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
      cases k with
      | zero => rfl
      | succ k => cases k <;> rfl

theorem white_step_erases_distinction :
    SameResponse (step false (word [true])) (step false (word [true,true])) := by
  rw [step_white_one,step_white_two]
  exact sameResponse_symm (tail_101_response [])

theorem initial_responses_differ : ¬ SameResponse (word [true]) (word [true,true]) :=
  fixed_driver_counterexample.2

theorem first_left_equal (left : Int → Bool) :
    ∀ p, p≤0 → evol (splice left (word [true])) 1 p =
      evol (splice left (word [true,true])) 1 p := by
  intro p hp
  change rule (splice left (word [true]) (p-1)) (splice left (word [true]) p)
      (splice left (word [true]) (p+1)) =
    rule (splice left (word [true,true]) (p-1)) (splice left (word [true,true]) p)
      (splice left (word [true,true]) (p+1))
  rw [show splice left (word [true]) (p-1)=left (p-1) by simp [splice,show p-1≤0 by omega],
      show splice left (word [true,true]) (p-1)=left (p-1) by simp [splice,show p-1≤0 by omega]]
  simp only [splice,hp,ite_true]
  by_cases hz : p=0
  · subst p; rfl
  · simp [show p+1≤0 by omega]

theorem first_right_sameResponse (left : Int → Bool) (hwhite : left 0=false) :
    SameResponse (rightPart (evol (splice left (word [true])) 1))
      (rightPart (evol (splice left (word [true,true])) 1)) := by
  rw [show 1=0+1 from rfl,rightPart_next,rightPart_next]
  simp only [evol,splice,Int.le_refl,ite_true,hwhite]
  exact white_step_erases_distinction

/-- All actual left columns agree, despite initially inequivalent right responses. -/
theorem same_left_forever (left : Int → Bool) (hwhite : left 0=false) :
    ∀ t p, p≤0 → evol (splice left (word [true])) t p =
      evol (splice left (word [true,true])) t p := by
  intro t p hp
  cases t with
  | zero => simp [evol,splice,hp]
  | succ t =>
      have h := (feedback_left_equal (first_left_equal left)
        (first_right_sameResponse left hwhite) t).1 p hp
      simpa only [evol_restart,Nat.add_comm 1 t] using h

def single : Int → Bool := splice (fun _ => false) (word [true])
def double : Int → Bool := splice (fun _ => false) (word [true,true])

theorem single_support (p : Int) : single p = decide (p=1) := by
  by_cases hp : p≤0
  · simp [single,splice,hp,show p≠1 by omega]
  · by_cases h1 : p=1
    · subst p; rfl
    · have hn : 1≤p.toNat-1 := by omega
      obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
      simp [single,splice,hp,word,hk,List.getD,h1]

theorem double_support (p : Int) : double p = decide (p=1 ∨ p=2) := by
  by_cases hp : p≤0
  · simp [double,splice,hp,show p≠1 by omega,show p≠2 by omega]
  · by_cases h1 : p=1
    · subst p; rfl
    · by_cases h2 : p=2
      · subst p; rfl
      · have hn : 2≤p.toNat-1 := by omega
        obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
        simp [double,splice,hp,word,hk,List.getD,h1,h2]

theorem single_finite : FinConfig single := by
  refine ⟨1,?_⟩
  intro p hp
  rw [single_support]
  simp [show p≠1 by intro h; subst p; simp at hp]

theorem double_finite : FinConfig double := by
  refine ⟨2,?_⟩
  intro p hp
  rw [double_support]
  simp [show p≠1 by intro h; subst p; simp at hp,
    show p≠2 by intro h; subst p; simp at hp]

theorem single_nonzero : ∃ p, single p=true := ⟨1,rfl⟩
theorem double_nonzero : ∃ p, double p=true := ⟨1,rfl⟩

theorem configurations_differ : single≠double := by
  intro h
  have he := congrFun h 2
  change false=true at he
  cases he

theorem same_actual_left : ∀ t p, p≤0 → evol single t p=evol double t p :=
  same_left_forever (fun _ => false) rfl

theorem same_actual_center (t : Nat) : evol single t 0=evol double t 0 :=
  same_actual_left t 0 (by omega)

theorem same_actual_right_head (t : Nat) : evol single t 1=evol double t 1 := by
  cases t with
  | zero => rfl
  | succ t =>
      have h := (feedback_left_equal (first_left_equal (fun _ => false))
        (first_right_sameResponse (fun _ => false) rfl) t).2
      have he := (sameResponse_observe h).1
      change evol (evol single 1) t 1=evol (evol double 1) t 1 at he
      simpa only [evol_restart,Nat.add_comm 1 t] using he

theorem initial_rights_not_sameResponse : ¬ SameResponse (rightPart single) (rightPart double) := by
  simpa only [single,double,rightPart_splice] using initial_responses_differ

theorem center_not_eventually_constant : ¬ ∃ T b, ∀ t, T≤t → evol single t 0=b :=
  Rule30FiniteConfigs.no_column_eventually_constant_finite single_finite single_nonzero 0

theorem right_head_not_eventually_constant : ¬ ∃ T b, ∀ t, T≤t → evol single t 1=b :=
  Rule30FiniteConfigs.no_column_eventually_constant_finite single_finite single_nonzero 1

/-- A genuine finite feedback counterexample, without an eventually constant trace. -/
theorem finite_feedback_counterexample :
    FinConfig single ∧ FinConfig double ∧ single≠double ∧
    (∀ t, evol single t 0=evol double t 0) ∧
    (∀ t, evol single t 1=evol double t 1) ∧
    (¬ ∃ T b, ∀ t, T≤t → evol single t 0=b) ∧
    (¬ ∃ T b, ∀ t, T≤t → evol single t 1=b) ∧
    ¬ SameResponse (rightPart single) (rightPart double) :=
  ⟨single_finite,double_finite,configurations_differ,same_actual_center,
    same_actual_right_head,center_not_eventually_constant,right_head_not_eventually_constant,
    initial_rights_not_sameResponse⟩

end Rule30Submission.Feedback

/-!
# A local obstruction to masking the first period doubling

This is a statement about five temporal columns satisfying the triangular
update, not about the vertical center column. If the second column reverses
color after an even half-period while the next two repeat, the OR of the
first two columns cannot stay black forever. A full-clock hypothesis on the
first column is explicit. No finite-tail period-detection theorem or prize
problem is proved here.
-/



namespace Rule30Submission.Clocks

open Rule30Submission.Response

private theorem mask_zero (a ah b c d : Bool)
    (h0 : (a || b)=true) (hh : (ah || !b)=true)
    (h1 : (xor a (b || c) || xor b (c || d))=true)
    (hh1 : (xor ah (!b || c) || xor (!b) (c || d))=true)
    (hk : xor a ah=false) : c=false ∧ d=false := by
  cases a <;> cases ah <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem difference_step (a ah b c : Bool) :
    xor (xor a (b || c)) (xor ah (!b || c)) = xor (xor a ah) (!c) := by
  cases a <;> cases ah <;> cases b <;> cases c <;> rfl

private theorem flip_sum (k b c : Bool) :
    xor (xor k (!c)) (xor b c) = !xor k b := by
  cases k <;> cases b <;> cases c <;> rfl

private theorem xor_not_right (a b : Bool) : xor a (!b)=!xor a b := by
  cases a <;> cases b <;> rfl

/-- An even half-clock cannot hide this particular clock onset behind constant OR. -/
theorem no_constant_OR_at_onset (a b c d e : Nat → Bool) (n : Nat)
    (ha : ∀ t, a (t+1)=xor (a t) (b t || c t))
    (hb : ∀ t, b (t+1)=xor (b t) (c t || d t))
    (hc : ∀ t, c (t+1)=xor (c t) (d t || e t))
    (haper : ∀ t, a (t+2*(2*n))=a t)
    (hanti : ∀ t, b (t+2*n)=!b t)
    (hcper : ∀ t, c (t+2*n)=c t)
    (hdper : ∀ t, d (t+2*n)=d t) :
    ¬ ∀ t, (a t || b t)=true := by
  intro hor
  let K (t : Nat) := xor (a t) (a (t+2*n))
  have Kstep (t : Nat) : K (t+1)=xor (K t) (!c t) := by
    dsimp [K]
    rw [show t+1+2*n=(t+2*n)+1 by omega,ha,ha,hanti,hcper]
    exact difference_step _ _ _ _
  have Kzero (t : Nat) (hk : K t=false) : c t=false ∧ d t=false := by
    apply mask_zero (a t) (a (t+2*n)) (b t) (c t) (d t) (hor t) ?_ ?_ ?_ hk
    · simpa only [hanti] using hor (t+2*n)
    · simpa only [ha,hb] using hor (t+1)
    · have h := hor ((t+2*n)+1)
      simpa only [ha,hb,hanti,hcper,hdper] using h
  have cd (t : Nat) : (c t || d t)=c t := by
    cases hct : c t with
    | true => rfl
    | false =>
        have hdt : d t=false := by
          cases hkt : K t with
          | false => exact (Kzero t hkt).2
          | true =>
              have hnext : K (t+1)=false := by rw [Kstep,hkt,hct]; rfl
              have hcn := (Kzero (t+1) hnext).1
              rw [hc,hct] at hcn
              cases hdt : d t <;> cases het : e t <;> simp_all
        rw [hdt]
        rfl
  let f (t : Nat) := xor (K t) (b t)
  have fstep (t : Nat) : f (t+1)=!f t := by
    dsimp [f]
    rw [Kstep,hb,cd]
    exact flip_sum _ _ _
  have f_even : ∀ m t, f (t+2*m)=f t := by
    intro m
    induction m with
    | zero => intro t; rfl
    | succ m ih =>
        intro t
        rw [show t+2*(m+1)=(t+2*m+1)+1 by omega,fstep,fstep,ih]
        exact Bool.not_not _
  have Kper (t : Nat) : K (t+2*n)=K t := by
    dsimp [K]
    rw [show t+2*n+2*n=t+2*(2*n) by omega,haper]
    exact Bool.xor_comm _ _
  have f_anti (t : Nat) : f (t+2*n)=!f t := by
    dsimp [f]
    rw [Kper,hanti]
    exact xor_not_right _ _
  have he := f_even n 0
  rw [f_anti] at he
  cases hf : f 0 <;> simp [hf] at he

theorem iterate_column_step (x : State) (k t : Nat) :
    iterate x (t+1) k=xor (iterate x t k)
      (iterate x t (k+1) || iterate x t (k+2)) := rfl

/-- The OR cannot even have the shorter half-clock: that would make it constant. -/
theorem OR_not_half_period (a b c d e : Nat → Bool) (n : Nat)
    (ha : ∀ t, a (t+1)=xor (a t) (b t || c t))
    (hb : ∀ t, b (t+1)=xor (b t) (c t || d t))
    (hc : ∀ t, c (t+1)=xor (c t) (d t || e t))
    (haper : ∀ t, a (t+2*(2*n))=a t)
    (hanti : ∀ t, b (t+2*n)=!b t)
    (hcper : ∀ t, c (t+2*n)=c t)
    (hdper : ∀ t, d (t+2*n)=d t) :
    ¬ ∀ t, (a (t+2*n) || b (t+2*n))=(a t || b t) := by
  intro hs
  apply no_constant_OR_at_onset a b c d e n ha hb hc haper hanti hcper hdper
  intro t
  cases hbt : b t with
  | true => simp
  | false =>
      have ht := hs t
      rw [hanti,hbt] at ht
      simpa using ht.symm

/-- One more column to the left must retain the larger clock as well. -/
theorem predecessor_not_half_period (z a b c d e : Nat → Bool) (n : Nat)
    (hz : ∀ t, z (t+1)=xor (z t) (a t || b t))
    (ha : ∀ t, a (t+1)=xor (a t) (b t || c t))
    (hb : ∀ t, b (t+1)=xor (b t) (c t || d t))
    (hc : ∀ t, c (t+1)=xor (c t) (d t || e t))
    (haper : ∀ t, a (t+2*(2*n))=a t)
    (hanti : ∀ t, b (t+2*n)=!b t)
    (hcper : ∀ t, c (t+2*n)=c t)
    (hdper : ∀ t, d (t+2*n)=d t) :
    ¬ ∀ t, z (t+2*n)=z t := by
  intro hzper
  apply OR_not_half_period a b c d e n ha hb hc haper hanti hcper hdper
  intro t
  have h1 := hz (t+2*n)
  rw [show t+2*n+1=(t+1)+2*n by omega,hzper,hzper,hz] at h1
  cases hz0 : z t <;> cases ho0 : (a t || b t) <;>
    cases hoH : (a (t+2*n) || b (t+2*n)) <;> simp_all

/-- Application to the actual triangular orbit, with every clock premise explicit. -/
theorem orbit_onset_not_constant_OR (x : State) (k n : Nat)
    (ha : ∀ t, iterate x (t+2*(2*n)) k=iterate x t k)
    (hb : ∀ t, iterate x (t+2*n) (k+1)=!iterate x t (k+1))
    (hc : ∀ t, iterate x (t+2*n) (k+2)=iterate x t (k+2))
    (hd : ∀ t, iterate x (t+2*n) (k+3)=iterate x t (k+3)) :
    ¬ ∀ t, (iterate x t k || iterate x t (k+1))=true := by
  apply no_constant_OR_at_onset (fun t => iterate x t k)
    (fun t => iterate x t (k+1)) (fun t => iterate x t (k+2))
    (fun t => iterate x t (k+3)) (fun t => iterate x t (k+4)) n
    (iterate_column_step x k) ?_ ?_ ha hb hc hd
  · intro t
    simpa only [Nat.add_assoc] using iterate_column_step x (k+1) t
  · intro t
    simpa only [Nat.add_assoc] using iterate_column_step x (k+2) t

end Rule30Submission.Clocks

/-!
# Finite temporal-profile certificates for arbitrary finite spatial widths

A checked pool of temporal profile pairs is closed under adjoining a column
on the left. Starting from the finite zero tail therefore covers every finite
width at the specified full clock. A separately checked property can propagate
a shorter head clock to every spatial column. The clock size is explicit;
this module does not establish an arbitrary-clock induction or a prize result.
-/



namespace Rule30Submission.FiniteClockCertificate

open Rule30Submission.Response

structure Node where
  b : Nat
  c : Nat
  a0 : Nat
  a1 : Nat
deriving DecidableEq, Repr

def pat (P a t : Nat) : Bool := a.testBit (t%P)

def accum (u : Nat → Bool) : Nat → Bool
  | 0 => false
  | t+1 => xor (accum u t) (u t)

def forcing (P b c t : Nat) : Bool := pat P b t || pat P c t

def pairMem (pool : List Node) (b c : Nat) : Bool :=
  pool.any fun e => decide (e.b=b ∧ e.c=c)

theorem pairMem_iff (pool : List Node) (b c : Nat) :
    pairMem pool b c=true ↔ ∃ e, e∈pool ∧ e.b=b ∧ e.c=c := by
  simp [pairMem,List.any_eq_true]

def nodeCheck (P : Nat) (pool : List Node) (e : Node) : Bool :=
  ((List.range P).all fun t => decide (pat P e.a0 t=accum (forcing P e.b e.c) t)) &&
  ((List.range P).all fun t => decide (pat P e.a1 t= !accum (forcing P e.b e.c) t)) &&
  (if accum (forcing P e.b e.c) P then true
   else pairMem pool e.a0 e.b && pairMem pool e.a1 e.b)

def poolCheck (P : Nat) (pool : List Node) : Bool :=
  pairMem pool 0 0 && pool.all (nodeCheck P pool)

def Covered (P : Nat) (pool : List Node) (f g : Nat → Bool) : Prop :=
  ∃ e, e∈pool ∧ (∀ t, f t=pat P e.b t) ∧ (∀ t, g t=pat P e.c t)

theorem periodic_mod {P : Nat} {f : Nat → Bool}
    (h : ∀ t, f (t+P)=f t) : ∀ t, f t=f (t%P) := by
  intro t
  have key : ∀ n r, f (r+P*n)=f r := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
        intro r
        rw [show r+P*(n+1)=(r+P*n)+P by rw [Nat.mul_add,Nat.mul_one,Nat.add_assoc],h,ih]
  simpa only [Nat.mod_add_div] using key (t/P) (t%P)

theorem periodic_add_mul {P : Nat} {f : Nat → Bool}
    (h : ∀ t, f (t+P)=f t) : ∀ n t, f (t+P*n)=f t := by
  intro n
  induction n with
  | zero => intro t; simp
  | succ n ih =>
      intro t
      rw [show t+P*(n+1)=(t+P*n)+P by rw [Nat.mul_add,Nat.mul_one,Nat.add_assoc],h,ih]

/-- On a purely periodic sequence an eventual period already holds from time zero. -/
theorem eventual_period_is_period (P H T : Nat) (hP : 0<P) (f : Nat → Bool)
    (hp : ∀ t, f (t+P)=f t) (he : ∀ t, T≤t → f (t+H)=f t) :
    ∀ t, f (t+H)=f t := by
  have bound : ∀ n, n≤P*n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ]; omega
  intro t
  have h := he (t+P*T) (by have := bound T; omega)
  rw [show t+P*T+H=(t+H)+P*T by omega,periodic_add_mul hp,periodic_add_mul hp] at h
  exact h

theorem accum_solution (f u : Nat → Bool)
    (hf : ∀ t, f (t+1)=xor (f t) (u t)) :
    ∀ t, f t=xor (f 0) (accum u t) := by
  intro t
  induction t with
  | zero => simp [accum]
  | succ t ih =>
      rw [hf,accum,ih]
      cases f 0 <;> cases accum u t <;> cases u t <;> rfl

theorem accum_return_false (P : Nat) (f u : Nat → Bool)
    (hf : ∀ t, f (t+1)=xor (f t) (u t)) (hp : f P=f 0) :
    accum u P=false := by
  have h := accum_solution f u hf P
  rw [hp] at h
  cases ha : f 0 <;> cases hb : accum u P <;> simp [ha,hb] at h ⊢

theorem pat_mod (P a t : Nat) : pat P a (t%P)=pat P a t := by
  simp [pat]

theorem covered_zero (P : Nat) (pool : List Node) (h : pairMem pool 0 0=true) :
    Covered P pool (fun _ => false) (fun _ => false) := by
  obtain ⟨e,he,hb,hc⟩ := (pairMem_iff pool 0 0).mp h
  refine ⟨e,he,?_,?_⟩ <;> intro t
  · rw [hb]; simp [pat]
  · rw [hc]; simp [pat]

theorem covered_predecessor (P : Nat) (hP : 0<P) (pool : List Node)
    (hcheck : poolCheck P pool=true) (f g h : Nat → Bool)
    (hf : ∀ t, f (t+1)=xor (f t) (g t || h t))
    (hp : ∀ t, f (t+P)=f t) (hcover : Covered P pool g h) :
    Covered P pool f g := by
  obtain ⟨e,he,hg,hh⟩ := hcover
  have hchecks : pairMem pool 0 0=true ∧ pool.all (nodeCheck P pool)=true := by
    simpa only [poolCheck,Bool.and_eq_true] using hcheck
  have hall := hchecks.2
  have hc := List.all_eq_true.mp hall e he
  simp only [nodeCheck,Bool.and_eq_true] at hc
  have hforce : ∀ t, f (t+1)=xor (f t) (forcing P e.b e.c t) := by
    intro t
    rw [hf,hg,hh]
    rfl
  have hret : accum (forcing P e.b e.c) P=false :=
    accum_return_false P f _ hforce (by simpa using hp 0)
  have hclosed : pairMem pool e.a0 e.b=true ∧ pairMem pool e.a1 e.b=true := by
    simpa only [hret,Bool.false_eq_true,ite_false,Bool.and_eq_true] using hc.2
  have hsol := accum_solution f _ hforce
  cases hf0 : f 0 with
  | false =>
      obtain ⟨a,ha,ha0,hab⟩ := (pairMem_iff pool e.a0 e.b).mp hclosed.1
      refine ⟨a,ha,?_,?_⟩
      · intro t
        rw [ha0,periodic_mod hp t,hsol,hf0]
        have ht := List.all_eq_true.mp hc.1.1 (t%P) (List.mem_range.mpr (Nat.mod_lt _ hP))
        have heq := of_decide_eq_true ht
        simpa only [Bool.false_xor,pat_mod] using heq.symm
      · intro t; rw [hab,hg]
  | true =>
      obtain ⟨a,ha,ha1,hab⟩ := (pairMem_iff pool e.a1 e.b).mp hclosed.2
      refine ⟨a,ha,?_,?_⟩
      · intro t
        rw [ha1,periodic_mod hp t,hsol,hf0]
        have ht := List.all_eq_true.mp hc.1.2 (t%P) (List.mem_range.mpr (Nat.mod_lt _ hP))
        have heq := of_decide_eq_true ht
        simpa only [Bool.true_xor,pat_mod] using heq.symm
      · intro t; rw [hab,hg]

/-- Pool closure covers every spatial width; no width bound is part of the certificate. -/
theorem covers_finite_family (P : Nat) (hP : 0<P) (pool : List Node)
    (hcheck : poolCheck P pool=true) (x : Nat → Nat → Bool) (W : Nat)
    (hstep : ∀ k t, x k (t+1)=xor (x k t) (x (k+1) t || x (k+2) t))
    (hper : ∀ k t, x k (t+P)=x k t)
    (hzero : ∀ k, W≤k → ∀ t, x k t=false) :
    ∀ k, Covered P pool (x k) (x (k+1)) := by
  have descend : ∀ n k, W≤k+n → Covered P pool (x k) (x (k+1)) := by
    intro n
    induction n with
    | zero =>
        intro k hk
        have h0 : x k=(fun _ => false) := funext (hzero k (by omega))
        have h1 : x (k+1)=(fun _ => false) := funext (hzero (k+1) (by omega))
        rw [h0,h1]
        have hchecks : pairMem pool 0 0=true ∧ pool.all (nodeCheck P pool)=true := by
          simpa only [poolCheck,Bool.and_eq_true] using hcheck
        exact covered_zero P pool hchecks.1
    | succ n ih =>
        intro k hk
        apply covered_predecessor P hP pool hcheck (x k) (x (k+1)) (x (k+2))
          (hstep k) (hper k)
        simpa only [Nat.add_assoc] using ih (k+1) (by omega)
  intro k
  exact descend W k (by omega)

def periodCheck (P H a : Nat) : Bool :=
  (List.range P).all fun t => decide (pat P a (t+H)=pat P a t)

theorem periodCheck_iff (P H a : Nat) (hP : 0<P) :
    periodCheck P H a=true ↔ ∀ t, pat P a (t+H)=pat P a t := by
  constructor
  · intro h t
    have hh := List.all_eq_true.mp h (t%P) (List.mem_range.mpr (Nat.mod_lt _ hP))
    have heq := of_decide_eq_true hh
    simpa only [pat,Nat.add_mod,Nat.mod_mod] using heq
  · intro h
    apply List.all_eq_true.mpr
    intro t ht
    exact decide_eq_true (h t)

def detectionCheck (P H : Nat) (pool : List Node) : Bool :=
  pool.all fun e => if periodCheck P H e.b then periodCheck P H e.c else true

theorem periodCheck_mod_clock (P H a : Nat) :
    periodCheck P (H%P) a=periodCheck P H a := by
  simp [periodCheck,pat,Nat.add_mod]

theorem detectionCheck_mod_clock (P H : Nat) (pool : List Node) :
    detectionCheck P (H%P) pool=detectionCheck P H pool := by
  simp only [detectionCheck,periodCheck_mod_clock]

theorem covered_period_propagates (P H : Nat) (hP : 0<P) (pool : List Node)
    (hdetect : detectionCheck P H pool=true) {f g : Nat → Bool}
    (hcover : Covered P pool f g) (hf : ∀ t, f (t+H)=f t) :
    ∀ t, g (t+H)=g t := by
  obtain ⟨e,he,hfcode,hgcode⟩ := hcover
  have hb : periodCheck P H e.b=true := (periodCheck_iff P H e.b hP).mpr (by
    intro t
    rw [← hfcode,← hfcode,hf])
  have hc := List.all_eq_true.mp hdetect e he
  simp only [hb,ite_true] at hc
  have hcp := (periodCheck_iff P H e.c hP).mp hc
  intro t
  rw [hgcode,hgcode,hcp]

/-- A successful detection check turns one head clock into a clock for every column. -/
theorem finite_family_clock_detected (P H : Nat) (hP : 0<P) (pool : List Node)
    (hcheck : poolCheck P pool=true) (hdetect : detectionCheck P H pool=true)
    (x : Nat → Nat → Bool) (W : Nat)
    (hstep : ∀ k t, x k (t+1)=xor (x k t) (x (k+1) t || x (k+2) t))
    (hper : ∀ k t, x k (t+P)=x k t)
    (hzero : ∀ k, W≤k → ∀ t, x k t=false)
    (hhead : ∀ t, x 0 (t+H)=x 0 t) : ∀ k t, x k (t+H)=x k t := by
  have covered := covers_finite_family P hP pool hcheck x W hstep hper hzero
  intro k
  induction k with
  | zero => exact hhead
  | succ k ih => exact covered_period_propagates P H hP pool hdetect (covered k) ih

theorem iterate_restart (x : State) (a : Nat) :
    ∀ b, iterate (iterate x a) b=iterate x (a+b)
  | 0 => rfl
  | b+1 => by rw [iterate,iterate_restart x a b]; rfl

theorem iterate_period_of_return (x : State) (P : Nat) (hp : iterate x P=x) :
    ∀ t, iterate x (t+P)=iterate x t := by
  intro t
  rw [Nat.add_comm t P,← iterate_restart,hp]

theorem iterate_zero_tail (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false) :
    ∀ t k, W≤k → iterate x t k=false := by
  intro t
  induction t with
  | zero => exact hx
  | succ t ih =>
      intro k hk
      change xor (iterate x t k) (iterate x t (k+1) || iterate x t (k+2))=false
      rw [ih k hk,ih (k+1) (by omega),ih (k+2) (by omega)]
      rfl

/-- Specialization to the actual triangular map, with finite support and full clock explicit. -/
theorem finite_state_clock_detected (P H : Nat) (hP : 0<P) (pool : List Node)
    (hcheck : poolCheck P pool=true) (hdetect : detectionCheck P H pool=true)
    (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x P=x)
    (hhead : ∀ t, iterate x (t+H) 0=iterate x t 0) : iterate x H=x := by
  have hper := iterate_period_of_return x P hfull
  have hfin := iterate_zero_tail x W hx
  have hall := finite_family_clock_detected P H hP pool hcheck hdetect
    (fun k t => iterate x t k) W (fun _ _ => rfl)
    (fun k t => congrFun (hper t) k) (fun k hk t => hfin t k hk) hhead
  funext k
  simpa only [Nat.zero_add,iterate] using hall k 0

theorem finite_state_eventual_clock_detected (P H : Nat) (hP : 0<P) (pool : List Node)
    (hcheck : poolCheck P pool=true) (hdetect : detectionCheck P H pool=true)
    (x : State) (W T : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x P=x)
    (hhead : ∀ t, T≤t → iterate x (t+H) 0=iterate x t 0) : iterate x H=x := by
  apply finite_state_clock_detected P H hP pool hcheck hdetect x W hx hfull
  exact eventual_period_is_period P H T hP (fun t => iterate x t 0)
    (fun t => congrFun (iterate_period_of_return x P hfull t) 0) hhead

end Rule30Submission.FiniteClockCertificate

/-!
# A clock-sixteen certificate, valid at every finite spatial width

This checks temporal profile closure and shorter-clock detection using the
unchanged Lean kernel. The full clock is fixed at sixteen; no center-column
period or arbitrary-clock theorem is asserted.
-/



namespace Rule30Submission.FiniteClockSixteen

open Rule30Submission.Response Rule30Submission.FiniteClockCertificate

def pool16 : List Node := [
  Node.mk 0 0 0 65535,
  Node.mk 65535 0 43690 21845,
  Node.mk 43690 65535 43690 21845,
  Node.mk 21845 65535 43690 21845,
  Node.mk 43690 43690 52428 13107,
  Node.mk 21845 43690 43690 21845,
  Node.mk 43690 21845 43690 21845,
  Node.mk 21845 21845 26214 39321,
  Node.mk 52428 43690 46260 19275,
  Node.mk 13107 43690 53970 11565,
  Node.mk 26214 21845 23130 42405,
  Node.mk 39321 21845 38550 26985,
  Node.mk 46260 52428 43176 22359,
  Node.mk 19275 52428 35466 30069,
  Node.mk 53970 13107 41634 23901,
  Node.mk 11565 13107 10794 54741,
  Node.mk 23130 26214 21588 43947,
  Node.mk 42405 26214 47802 17733,
  Node.mk 38550 39321 60138 5397,
  Node.mk 26985 39321 44718 20817,
  Node.mk 43176 46260 55080 10455,
  Node.mk 22359 46260 42330 23205,
  Node.mk 35466 19275 36210 29325,
  Node.mk 30069 19275 21930 43605,
  Node.mk 41634 53970 41820 23715,
  Node.mk 23901 53970 38250 27285,
  Node.mk 10794 11565 13770 51765,
  Node.mk 54741 11565 43350 22185,
  Node.mk 21588 23130 27540 37995,
  Node.mk 43947 23130 44370 21165,
  Node.mk 47802 42405 54570 10965,
  Node.mk 17733 42405 47430 18105,
  Node.mk 60138 38550 43860 21675,
  Node.mk 5397 38550 58650 6885,
  Node.mk 44718 26985 46410 19125,
  Node.mk 20817 26985 20910 44625,
  Node.mk 55080 43176 21808 43727,
  Node.mk 10455 43176 12458 53077,
  Node.mk 42330 22359 23146 42389,
  Node.mk 23205 22359 38234 27301,
  Node.mk 36210 35466 2732 62803,
  Node.mk 29325 35466 21258 44277,
  Node.mk 21930 30069 42666 22869,
  Node.mk 43605 30069 21926 43609,
  Node.mk 41820 41634 15700 49835,
  Node.mk 23715 41634 21698 43837,
  Node.mk 38250 23901 27050 38485,
  Node.mk 27285 23901 43670 21865,
  Node.mk 13770 10794 54604 10931,
  Node.mk 51765 10794 19498 46037,
  Node.mk 43350 54741 22170 43365,
  Node.mk 22185 54741 25942 39593,
  Node.mk 27540 21588 43672 21863,
  Node.mk 37995 21588 26538 38997,
  Node.mk 44370 43947 13650 51885,
  Node.mk 21165 43947 21194 44341,
  Node.mk 54570 47802 21804 43731,
  Node.mk 10965 47802 11434 54101,
  Node.mk 47430 17733 22138 43397,
  Node.mk 18105 17733 34134 31401,
  Node.mk 43860 60138 19796 45739,
  Node.mk 21675 60138 21682 43853,
  Node.mk 58650 5397 23018 42517,
  Node.mk 6885 5397 60070 5465,
  Node.mk 46410 44718 10932 54603,
  Node.mk 19125 44718 19242 46293,
  Node.mk 20910 20817 40618 24917,
  Node.mk 44625 20817 21918 43617]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem pool16_checked : poolCheck 16 pool16=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem detection16_checked :
    (List.range 16).all (fun H => detectionCheck 16 H pool16)=true := by decide +kernel

theorem detection16_all_head_clocks (H : Nat) : detectionCheck 16 H pool16=true := by
  have h := List.all_eq_true.mp detection16_checked (H%16)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simpa only [detectionCheck_mod_clock] using h

/-- No finite-width orbit whose full clock divides sixteen can hide a shorter head clock. -/
theorem period_detected (x : State) (W H : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, iterate x (t+H) 0=iterate x t 0) : iterate x H=x := by
  exact finite_state_clock_detected 16 H (by decide) pool16 pool16_checked
    (detection16_all_head_clocks H) x W hx hfull hhead

theorem period8_detected (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, iterate x (t+8) 0=iterate x t 0) : iterate x 8=x :=
  period_detected x W 8 hx hfull hhead

theorem period4_detected (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, iterate x (t+4) 0=iterate x t 0) : iterate x 4=x :=
  period_detected x W 4 hx hfull hhead

theorem period2_detected (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, iterate x (t+2) 0=iterate x t 0) : iterate x 2=x :=
  period_detected x W 2 hx hfull hhead

theorem period1_detected (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, iterate x (t+1) 0=iterate x t 0) : iterate x 1=x :=
  period_detected x W 1 hx hfull hhead

theorem eventual_period_detected (x : State) (W H T : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, T≤t → iterate x (t+H) 0=iterate x t 0) : iterate x H=x := by
  exact finite_state_eventual_clock_detected 16 H (by decide) pool16 pool16_checked
    (detection16_all_head_clocks H) x W T hx hfull hhead

/-- A hidden shorter head clock in this full-clock range requires an infinite initial tail. -/
theorem period_loss_requires_infinite_tail (x : State) (H T : Nat)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, T≤t → iterate x (t+H) 0=iterate x t 0)
    (hloss : iterate x H≠x) : ∀ W, ∃ k, W≤k ∧ x k=true := by
  intro W
  apply Classical.byContradiction
  intro hnone
  have hfin : ∀ k, W≤k → x k=false := by
    intro k hk
    cases hb : x k with
    | false => rfl
    | true => exact False.elim (hnone ⟨k,hk,hb⟩)
  exact hloss (eventual_period_detected x W H T hfin hfull hhead)

end Rule30Submission.FiniteClockSixteen
