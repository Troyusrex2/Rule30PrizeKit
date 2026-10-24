---
Template: ComputationalEssay
Name: Controlled responses and finite-support observability limits in Rule 30
Author: Troy Lowry; OpenAI Codex
Date: 2026-10-24
Description: Arbitrary-driver response equivalence, sound terminal rewrites, and explicit infinite-tail counterexamples
Abstract: Responses of a right half to every left-boundary input are characterized exactly by two observations of a triangular diagonal map. Terminal rewrites 011 to 01 and 101 to 11 preserve the complete center trace with every common initial left half. Explicit eight-periodic infinite tails show that OR alone need not recover the head and that a period-two head need not detect a full period-eight state. Finite-tail completeness and the Rule 30 Prize problems remain open.
Keywords: [Rule 30, controlled systems, observability, Lean, infinite tails]
---

## Scope and provenance

This is a partial contribution developed by Troy Lowry with OpenAI Codex. It
builds on the kit's driven right half in Rule30Ether and whole-line evolution
in Rule30Realization. No literature-priority claim is made. The essay is
prepared for human review and has not been sent to the prize API.

The terminal rewrites can change a finite row's right edge without changing
its center trace. For example, the two rows with black cells only at positions
{2,3} and {2}, respectively, have identical center traces at every time. Their
left edges agree; this does not refute recovering a left edge from the trace.
The general theorem allows every common initial left half and every shared
finite prefix before the displayed terminal word.

## Exact response equivalence

Index a right-half state x by 0,1,... for physical positions 1,2,... . Define

    Q(x)(k) = x(k) XOR (x(k+1) OR x(k+2)).
    F_b(x)  = (b XOR (x(0) OR x(1))) :: Q(x).

The second formula is exactly one Rule 30 step with left boundary bit b. Two
right states have equal head outputs for every boundary-input sequence and
every time if and only if, for every n, both the head and the OR of the first
two cells of Q^n(x) agree. The infinite response tree is therefore replaced
by two observations along one deterministic orbit. The theorem places no
finite-support restriction on this equivalence.

For every common finite prefix, terminal 011 followed by zeros can be
replaced by 01, and terminal 101 followed by zeros by 11. Both replacements
preserve responses to all boundary inputs for all times. A separate induction
shows that this equivalence remains sound with actual feedback through the
center: if initial left halves, including the center, agree, they agree at
every later time. Thus both terminal rewrites preserve the complete center
trace in the full Rule 30 system, including when both starting rows are finite.

No converse from a single prescribed driver is proved. In fact, right states
1 and 11 have the same head output forever under the constantly zero driver,
but are not universally response equivalent. This driver is not asserted to
extend to a finite whole-line orbit. A second example, packed states 42 and
70, agrees through thirteen observations for every driver but is not
universally equivalent. Checking only 2W-1 observations is insufficient at W=7.

## Why the support and observation hypotheses matter

Write an infinite row from its head toward the right. The two starts

    x = 1100(1101)...
    y = 0110(01)...

use parenthesized blocks repeated forever. Both complete Q orbits have period
dividing eight. Their head traces differ, but the OR of the first two cells
is the same nonconstant sequence at every time. At time two, the next OR,
of cells one and two, differs. The common OR alone cannot recover the head
or the next OR. These states are not universally response equivalent, because
that relation observes the head as well.

A third start, 1100(0001)..., has a head trace of least period two, whereas its
complete Q orbit has least period eight. All three starts are proved to have
infinite support. A power-of-two orbit period cannot replace finite support
in a proposed head-period detection theorem. No finite-tail conjecture is
refuted or proved by these examples.

The proofs use explicit temporal profile tables, verify their scalar update
at every depth, and then identify all iterates by induction. The finite search
that found the tables is not a proof premise. No part of this essay excludes
an eventual center period or proves a Rule 30 Prize problem.

## Independent finite controls

The first calculation compares terminal rewrites in 104 complete Rule 30
experiments with random common left halves and prefixes. The second compares
all three profile tables with built-in Rule 30 on finite causal cones.
These controls do not replace the unbounded kernel proofs.

```wl
(* Independent finite samples using the built-in Rule 30 evolution.
   Unbounded statements and feedback soundness are proved in Lean. *)
ClearAll[controlledResponseReport];
controlledResponseReport[] := BlockRandom[
  SeedRandom[20261024];
  Module[{cases},
    cases = Flatten[Table[Module[{left, prefix, old, new, ca, cb, center = 9},
      left = RandomInteger[1, 9];
      prefix = RandomInteger[1, n];
      {old, new} = If[rule == 0, {{0,1,1}, {0,1,0}}, {{1,0,1}, {1,1,0}}];
      ca = Flatten@CellularAutomaton[30, {Join[left, prefix, old], 0}, {128, {{center}}}];
      cb = Flatten@CellularAutomaton[30, {Join[left, prefix, new], 0}, {128, {{center}}}];
      <|"PrefixLength" -> n, "Rewrite" -> If[rule == 0, "011->01", "101->11"],
        "Horizon" -> 128, "ObservationCount" -> Length[ca], "SameCenterTracePrefix" -> SameQ[ca, cb]|>
    ], {n, 0, 12}, {rule, 0, 1}, {sample, 1, 4}], 2];
    <|"FiniteSamplesOnly" -> True, "UnboundedProofReplaced" -> False,
      "FullProblemClaim" -> False, "CaseCount" -> Length[cases],
      "AllPassed" -> And@@Lookup[cases, "SameCenterTracePrefix"], "Cases" -> cases|>
  ]
];

(* Compare all three infinite profile tables with actual finite Rule 30 cones. *)
ClearAll[profileCounterReport];
profileCounterReport[] := Module[{tables, h = 32, window = 8, counts},
  tables = {{45,43,186,166,101,149,86,89},
    {42,45,51,170,170,85,170,85}, {85,87,168,212,172,178,202,43}};
  counts = Table[Module[{profile, n, initial, ca, checks},
    profile[k_] := table[[If[k<4, k+1, 5+Mod[k-4,4]]]];
    n = window+2*h+2;
    initial = Table[BitAnd[profile[k], 1], {k, 0, n-1}];
    ca = CellularAutomaton[30, Join[ConstantArray[0,h+1], initial, ConstantArray[0,h+1]], h];
    checks = Flatten@Table[
      ca[[t+1, h+2+k+t]] == BitAnd[BitShiftRight[profile[k], Mod[t,8]],1],
      {t,0,h}, {k,0,window-1}];
    <|"ScalarCellsCompared"->Length[checks], "AllPassed"->And@@checks|>
  ], {table,tables}];
  <|"FiniteControlsOnly"->True, "FullProblemClaim"->False,
    "BuiltinRule30Cones"->Length[counts], "Cases"->counts,
    "AllPassed"->And@@Lookup[counts,"AllPassed"]|>
];

ClearAll[profileCounterDiagram];
profileCounterDiagram[] := Module[{tables, labels},
  tables = {{45,43,186,166,101,149,86,89},
    {42,45,51,170,170,85,170,85}, {85,87,168,212,172,178,202,43}};
  labels = {"First OR example", "Second OR example", "Head period 2; state period 8"};
  GraphicsRow[Table[ArrayPlot[
    Table[BitAnd[BitShiftRight[tables[[j,If[k<4,k+1,5+Mod[k-4,4]]]],t],1],
      {t,0,7},{k,0,11}], ColorRules->{0->White,1->Black},
    Frame->True, FrameTicks->None, Mesh->All, MeshStyle->LightGray,
    PlotLabel->Style[labels[[j]],12],
    (* ArrayPlot orders these as {{bottom,top},{left,right}}. *)
    FrameLabel->{{"position 0 through 11",None},{"time 0 through 7 from top",None}},
    ImageSize->320], {j,3}], ImageSize->1050]
];

{controlledResponseReport[], profileCounterReport[]}
```

The diagram shows eight times, from top to bottom, and the first twelve cells
of each infinite row. Black squares are black cells. The right tail repeats
from position four. The last panel's first column alternates while later
columns require eight times to repeat; the all-time claims are proved below.

```wl
profileCounterDiagram[]
```

## Exact embedded proof and full kernel replay

The source below contains both complete catalog modules, with only imports,
module/export wrappers and namespace names adapted for a standalone file.
It imports only official core modules and uses no additional axioms or native
decision procedures. A passing partial check does not establish an official
prize target.

```wl
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit = Environment["RULE30PRIZE_KIT"];
```

```wl
rule30Submission = LeanImportString["import Ruliology.CellularAutomata.Rule30Ether\nimport Ruliology.CellularAutomata.Rule30Realization\nimport Ruliology.CellularAutomata.Rule30ZeroBoundary\n\nopen Ruliology.CellularAutomata\n\n/-!\n# Controlled responses and the triangular right-edge update\n\nThe response tree for every possible left driver is equivalent to alternating\nhead/OR observations of a triangular update. This is an exact controlled-system\nequivalence. A single prescribed driver is a different question; no prize\nproblem is solved here.\n-/\n\n\n\nnamespace Rule30Submission.Response\n\nopen Rule30Jen Rule30Ether\n\nabbrev State := Nat → Bool\n\ndef prepend (a : Bool) (x : State) : State\n  | 0 => a\n  | k+1 => x k\n\ndef diagonal (x : State) (k : Nat) : Bool :=\n  xor (x k) (x (k+1) || x (k+2))\n\ndef step (b : Bool) (x : State) : State :=\n  prepend (xor b (x 0 || x 1)) (diagonal x)\n\ndef run (c : Nat → Bool) (x : State) : Nat → State\n  | 0 => x\n  | t+1 => step (c t) (run c x t)\n\ndef asRight (x : State) (p : Nat) : Bool :=\n  if p=0 then false else x (p-1)\n\n/-- The controlled state uses zero-based indexing of the kit's positions 1,2,... . -/\ntheorem run_sound (c : Nat → Bool) (x : State) : ∀ t k,\n    run c x t k=drv c (asRight x) t (k+1) := by\n  intro t\n  induction t with\n  | zero => intro k; simp [run,drv,asRight]\n  | succ t ih =>\n      intro k\n      cases k with\n      | zero => simp [run,step,prepend,drv,rule,ih,drv_col0]\n      | succ k => simp [run,step,prepend,diagonal,drv,rule,ih,Nat.add_assoc]\n\ntheorem run_shift (c : Nat → Bool) (x : State) : ∀ n,\n    run c x (n+1)=run (fun j => c (j+1)) (step (c 0) x) n\n  | 0 => rfl\n  | n+1 => by\n      rw [run,run_shift c x n]\n      rfl\n\ndef ResponseEq : Nat → State → State → Prop\n  | 0,_,_ => True\n  | n+1,x,y => x 0=y 0 ∧ ∀ b, ResponseEq n (step b x) (step b y)\n\ntheorem responseEq_iff_runs (n : Nat) (x y : State) :\n    ResponseEq n x y ↔ ∀ c t, t<n → run c x t 0=run c y t 0 := by\n  induction n generalizing x y with\n  | zero => simp [ResponseEq]\n  | succ n ih =>\n      constructor\n      · intro h c t ht\n        cases t with\n        | zero => exact h.1\n        | succ t =>\n            rw [run_shift,run_shift]\n            exact (ih (step (c 0) x) (step (c 0) y)).mp (h.2 (c 0)) _ t (by omega)\n      · intro h\n        refine ⟨h (fun _ => false) 0 (by omega),fun b => ?_⟩\n        apply (ih _ _).mpr\n        intro c t ht\n        have he := h (prepend b c) (t+1) (by omega)\n        rw [run_shift,run_shift] at he\n        simpa only [prepend] using he\n\ntheorem diagonal_prepend (a : Bool) (x : State) : diagonal (prepend a x)=step a x := by\n  funext k\n  cases k <;> rfl\n\ntheorem step_prepend (b a : Bool) (x : State) :\n    step b (prepend a x)=prepend (xor b (a || x 0)) (step a x) := by\n  unfold step\n  rw [diagonal_prepend]\n  rfl\n\nprivate theorem xor_cancel (a b : Bool) : xor (xor a b) b=a := by\n  cases a <;> cases b <;> rfl\n\n/-- One arbitrary shared prefix cell costs one observation of the tail system. -/\ntheorem responseEq_all_prepend (n : Nat) (x y : State) :\n    (∀ a, ResponseEq (n+1) (prepend a x) (prepend a y)) ↔ ResponseEq n x y := by\n  induction n generalizing x y with\n  | zero => simp [ResponseEq,prepend]\n  | succ n ih =>\n      constructor\n      · intro h\n        have hhead : x 0=y 0 := by\n          have he := ((h false).2 false).1\n          simpa [step,prepend] using he\n        refine ⟨hhead,fun b => ?_⟩\n        apply (ih _ _).mp\n        intro a\n        have he := (h b).2 (xor a (b || x 0))\n        rw [step_prepend,step_prepend,← hhead,xor_cancel] at he\n        exact he\n      · intro h a\n        refine ⟨rfl,fun b => ?_⟩\n        rw [step_prepend,step_prepend,h.1]\n        exact (ih _ _).mpr (h.2 a) (xor b (a || y 0))\n\n/-- Two observations remove one triangular diagonal layer exactly. -/\ntheorem responseEq_two (n : Nat) (x y : State) :\n    ResponseEq (n+2) x y ↔ x 0=y 0 ∧ (x 0 || x 1)=(y 0 || y 1) ∧\n      ResponseEq n (diagonal x) (diagonal y) := by\n  constructor\n  · intro h\n    have hor : (x 0 || x 1)=(y 0 || y 1) := by\n      have he := (h.2 false).1\n      simpa [step,prepend] using he\n    refine ⟨h.1,hor,(responseEq_all_prepend n _ _).mp (fun a => ?_)⟩\n    have he := h.2 (xor a (x 0 || x 1))\n    change ResponseEq (n+1)\n      (prepend (xor (xor a (x 0 || x 1)) (x 0 || x 1)) (diagonal x))\n      (prepend (xor (xor a (x 0 || x 1)) (y 0 || y 1)) (diagonal y)) at he\n    rw [← hor,xor_cancel] at he\n    exact he\n  · rintro ⟨hhead,hor,hdiag⟩\n    refine ⟨hhead,fun b => ?_⟩\n    change ResponseEq (n+1) (prepend (xor b (x 0 || x 1)) (diagonal x))\n      (prepend (xor b (y 0 || y 1)) (diagonal y))\n    rw [hor]\n    exact (responseEq_all_prepend n _ _).mpr hdiag _\n\ndef iterate (x : State) : Nat → State\n  | 0 => x\n  | n+1 => diagonal (iterate x n)\n\ntheorem iterate_from (x : State) : ∀ n, iterate (diagonal x) n=iterate x (n+1)\n  | 0 => rfl\n  | n+1 => by rw [iterate,iterate_from x n]; rfl\n\ndef ObserveEq (x y : State) : Prop :=\n  x 0=y 0 ∧ (x 0 || x 1)=(y 0 || y 1)\n\ndef SameResponse (x y : State) : Prop := ∀ n, ResponseEq n x y\n\ntheorem sameResponse_shift {x y : State} (h : SameResponse x y) :\n    SameResponse (diagonal x) (diagonal y) :=\n  fun n => ((responseEq_two n x y).mp (h (n+2))).2.2\n\ntheorem sameResponse_observe {x y : State} (h : SameResponse x y) : ObserveEq x y :=\n  ⟨((responseEq_two 0 x y).mp (h 2)).1,((responseEq_two 0 x y).mp (h 2)).2.1⟩\n\nprivate theorem response_of_diagonal : ∀ n (x y : State),\n    (∀ k, ObserveEq (iterate x k) (iterate y k)) → ResponseEq n x y\n  | 0,_,_,_ => True.intro\n  | 1,x,y,h => ⟨(h 0).1,fun _ => True.intro⟩\n  | n+2,x,y,h => (responseEq_two n x y).mpr ⟨(h 0).1,(h 0).2,\n      response_of_diagonal n (diagonal x) (diagonal y) (fun k => by\n        rw [iterate_from,iterate_from]\n        exact h (k+1))⟩\n\n/-- Exact equivalence for every boundary word and observation horizon. -/\ntheorem sameResponse_iff_diagonal (x y : State) :\n    SameResponse x y ↔ ∀ k, ObserveEq (iterate x k) (iterate y k) := by\n  constructor\n  · intro h\n    have hi : ∀ k, SameResponse (iterate x k) (iterate y k) := by\n      intro k\n      induction k with\n      | zero => exact h\n      | succ k ih => exact sameResponse_shift ih\n    exact fun k => sameResponse_observe (hi k)\n  · intro h n\n    exact response_of_diagonal n x y h\n\ntheorem sameResponse_iff_drv (x y : State) :\n    SameResponse x y ↔ ∀ c t, drv c (asRight x) t 1=drv c (asRight y) t 1 := by\n  constructor\n  · intro h c t\n    rw [← run_sound c x t 0,← run_sound c y t 0]\n    exact (responseEq_iff_runs (t+1) x y).mp (h _) c t (by omega)\n  · intro h n\n    apply (responseEq_iff_runs n x y).mpr\n    intro c t _\n    rw [run_sound,run_sound]\n    exact h c t\n\ntheorem sameResponse_refl (x : State) : SameResponse x x :=\n  (sameResponse_iff_drv x x).mpr (fun _ _ => rfl)\n\ntheorem sameResponse_symm {x y : State} (h : SameResponse x y) : SameResponse y x :=\n  (sameResponse_iff_drv y x).mpr (fun c t => ((sameResponse_iff_drv x y).mp h c t).symm)\n\ntheorem sameResponse_trans {x y z : State} (h : SameResponse x y) (g : SameResponse y z) :\n    SameResponse x z :=\n  (sameResponse_iff_drv x z).mpr (fun c t =>\n    ((sameResponse_iff_drv x y).mp h c t).trans ((sameResponse_iff_drv y z).mp g c t))\n\ntheorem sameResponse_prepend {x y : State} (h : SameResponse x y) (a : Bool) :\n    SameResponse (prepend a x) (prepend a y) := by\n  intro n\n  cases n with\n  | zero => exact True.intro\n  | succ n => exact (responseEq_all_prepend n x y).mpr (h n) a\n\ndef withPrefix : List Bool → State → State\n  | [],x => x\n  | a::bs,x => prepend a (withPrefix bs x)\n\ntheorem sameResponse_withPrefix {x y : State} (h : SameResponse x y) (bs : List Bool) :\n    SameResponse (withPrefix bs x) (withPrefix bs y) := by\n  induction bs with\n  | nil => exact h\n  | cons a bs ih => exact sameResponse_prepend ih a\n\ndef word (bs : List Bool) (k : Nat) : Bool := bs.getD k false\n\ntheorem word_cons (a : Bool) (bs : List Bool) : word (a::bs)=prepend a (word bs) := by\n  funext k\n  cases k <;> rfl\n\ntheorem word_append (bs cs : List Bool) : word (bs++cs)=withPrefix bs (word cs) := by\n  induction bs with\n  | nil => rfl\n  | cons a bs ih =>\n      rw [List.cons_append,word_cons,withPrefix,ih]\n\ntheorem diagonal_011 : diagonal (word [false,true,true])=word [true,false,true] := by\n  funext k\n  cases k with\n  | zero => rfl\n  | succ k =>\n      cases k with\n      | zero => rfl\n      | succ k => cases k <;> rfl\n\ntheorem diagonal_01 : diagonal (word [false,true])=word [true,true] := by\n  funext k\n  cases k with\n  | zero => rfl\n  | succ k => cases k <;> rfl\n\ntheorem diagonal_101 : diagonal (word [true,false,true])=word [false,true,true] := by\n  funext k\n  cases k with\n  | zero => rfl\n  | succ k =>\n      cases k with\n      | zero => rfl\n      | succ k => cases k <;> rfl\n\ntheorem diagonal_11 : diagonal (word [true,true])=word [false,true] := by\n  funext k\n  cases k with\n  | zero => rfl\n  | succ k => cases k <;> rfl\n\nprivate theorem primitive_responses : ∀ n,\n    ResponseEq n (word [false,true,true]) (word [false,true]) ∧\n    ResponseEq n (word [true,false,true]) (word [true,true])\n  | 0 => ⟨True.intro,True.intro⟩\n  | 1 => ⟨⟨rfl,fun _ => True.intro⟩,⟨rfl,fun _ => True.intro⟩⟩\n  | n+2 => by\n      constructor\n      · apply (responseEq_two n _ _).mpr\n        refine ⟨rfl,rfl,?_⟩\n        rw [diagonal_011,diagonal_01]\n        exact (primitive_responses n).2\n      · apply (responseEq_two n _ _).mpr\n        refine ⟨rfl,rfl,?_⟩\n        rw [diagonal_101,diagonal_11]\n        exact (primitive_responses n).1\n\n/-- A terminal 011 may be replaced by 01, behind any finite shared prefix. -/\ntheorem tail_011_response (bs : List Bool) :\n    SameResponse (word (bs++[false,true,true])) (word (bs++[false,true])) := by\n  rw [word_append,word_append]\n  exact sameResponse_withPrefix (fun n => (primitive_responses n).1) bs\n\n/-- A terminal 101 may be replaced by 11, behind any finite shared prefix. -/\ntheorem tail_101_response (bs : List Bool) :\n    SameResponse (word (bs++[true,false,true])) (word (bs++[true,true])) := by\n  rw [word_append,word_append]\n  exact sameResponse_withPrefix (fun n => (primitive_responses n).2) bs\n\ntheorem tail_011_drv (bs : List Bool) (c : Nat → Bool) (t : Nat) :\n    drv c (asRight (word (bs++[false,true,true]))) t 1=\n      drv c (asRight (word (bs++[false,true]))) t 1 :=\n  (sameResponse_iff_drv _ _).mp (tail_011_response bs) c t\n\ntheorem tail_101_drv (bs : List Bool) (c : Nat → Bool) (t : Nat) :\n    drv c (asRight (word (bs++[true,false,true]))) t 1=\n      drv c (asRight (word (bs++[true,true]))) t 1 :=\n  (sameResponse_iff_drv _ _).mp (tail_101_response bs) c t\n\n/-- An equivalent finite test without branching over all boundary words. -/\ndef ObservationPrefix : Nat → State → State → Prop\n  | 0,_,_ => True\n  | 1,x,y => x 0=y 0\n  | n+2,x,y => ObserveEq x y ∧ ObservationPrefix n (diagonal x) (diagonal y)\n\ntheorem responseEq_iff_observationPrefix : ∀ n (x y : State),\n    ResponseEq n x y ↔ ObservationPrefix n x y\n  | 0,_,_ => Iff.rfl\n  | 1,_,_ => by simp [ResponseEq,ObservationPrefix]\n  | n+2,x,y => by\n      rw [responseEq_two,ObservationPrefix,← responseEq_iff_observationPrefix n]\n      exact and_assoc.symm\n\ninstance observeEqDecidable (x y : State) : Decidable (ObserveEq x y) :=\n  inferInstanceAs (Decidable (x 0=y 0 ∧ (x 0 || x 1)=(y 0 || y 1)))\n\ninstance observationPrefixDecidable : ∀ n (x y : State), Decidable (ObservationPrefix n x y)\n  | 0,_,_ => isTrue True.intro\n  | 1,x,y => inferInstanceAs (Decidable (x 0=y 0))\n  | n+2,x,y => @instDecidableAnd (ObserveEq x y)\n      (ObservationPrefix n (diagonal x) (diagonal y)) (observeEqDecidable x y)\n      (observationPrefixDecidable n (diagonal x) (diagonal y))\n\ndef shortWindowA : State := word [false,true,false,true,false,true]\ndef shortWindowB : State := word [false,true,true,false,false,false,true]\n\n/-- Width seven does not make thirteen observations a complete test. -/\ntheorem short_window_agreement : ResponseEq 13 shortWindowA shortWindowB := by\n  rw [responseEq_iff_observationPrefix]\n  decide\n\ntheorem short_window_not_sameResponse : ¬ SameResponse shortWindowA shortWindowB := by\n  intro h\n  have he := (sameResponse_iff_diagonal _ _).mp h 8\n  have hn : ¬ ObserveEq (iterate shortWindowA 8) (iterate shortWindowB 8) := by decide\n  exact hn he\n\ntheorem zero_driver_head (x : State) (hx : x 0=true) :\n    ∀ t, run (fun _ => false) x t 0=true := by\n  intro t\n  induction t with\n  | zero => exact hx\n  | succ t ih => simp [run,step,prepend,ih]\n\n/-- Agreement for one periodic driver does not imply universal response equality.\nThis externally imposed driver is not asserted to extend to a finite full row. -/\ntheorem fixed_driver_counterexample :\n    (∀ t, drv (fun _ => false) (asRight (word [true])) t 1=\n      drv (fun _ => false) (asRight (word [true,true])) t 1) ∧\n    ¬ SameResponse (word [true]) (word [true,true]) := by\n  constructor\n  · intro t\n    rw [← run_sound _ _ t 0,← run_sound _ _ t 0]\n    rw [zero_driver_head _ rfl,zero_driver_head _ rfl]\n  · intro h\n    have he := (sameResponse_iff_diagonal _ _).mp h 1\n    have hn : ¬ ObserveEq (iterate (word [true]) 1) (iterate (word [true,true]) 1) := by decide\n    exact hn he\n\ntheorem sameResponse_step {x y : State} (h : SameResponse x y) (b : Bool) :\n    SameResponse (step b x) (step b y) := fun n => (h (n+1)).2 b\n\nopen Rule30Realization\n\ndef rightPart (x : Int → Bool) (k : Nat) : Bool := x ((k:Int)+1)\n\ntheorem rightPart_next (x : Int → Bool) (t : Nat) :\n    rightPart (evol x (t+1))=step (evol x t 0) (rightPart (evol x t)) := by\n  funext k\n  cases k with\n  | zero => simp [rightPart,evol,step,prepend,rule]\n  | succ k =>\n      simp [rightPart,evol,step,prepend,diagonal,rule,Int.natCast_add,Int.add_assoc]\n      congr 1 <;> omega\n\n/-- Universal right-response equivalence remains sound under actual left feedback. -/\ntheorem feedback_left_equal {x y : Int → Bool}\n    (hleft : ∀ p, p≤0 → x p=y p) (hright : SameResponse (rightPart x) (rightPart y)) :\n    ∀ t, (∀ p, p≤0 → evol x t p=evol y t p) ∧\n      SameResponse (rightPart (evol x t)) (rightPart (evol y t)) := by\n  intro t\n  induction t with\n  | zero => exact ⟨hleft,hright⟩\n  | succ t ih =>\n      constructor\n      · intro p hp\n        have hhead : evol x t 1=evol y t 1 := (sameResponse_observe ih.2).1\n        change rule (evol x t (p-1)) (evol x t p) (evol x t (p+1)) =\n          rule (evol y t (p-1)) (evol y t p) (evol y t (p+1))\n        rw [ih.1 (p-1) (by omega),ih.1 p hp]\n        by_cases hz : p=0\n        · subst p; rw [show (0:Int)+1=1 by omega,hhead]\n        · rw [ih.1 (p+1) (by omega)]\n      · rw [rightPart_next,rightPart_next,ih.1 0 (by omega)]\n        exact sameResponse_step ih.2 _\n\ndef splice (left : Int → Bool) (right : State) (p : Int) : Bool :=\n  if p≤0 then left p else right (p.toNat-1)\n\ntheorem rightPart_splice (left : Int → Bool) (right : State) :\n    rightPart (splice left right)=right := by\n  funext k\n  simp [rightPart,splice,show ¬ (k:Int)+1≤0 by omega]\n\ntheorem splice_same_center (left : Int → Bool) {x y : State} (h : SameResponse x y) (t : Nat) :\n    evol (splice left x) t 0=evol (splice left y) t 0 := by\n  apply (feedback_left_equal (x:=splice left x) (y:=splice left y) ?_ ?_ t).1 0 (by omega)\n  · intro p hp\n    simp [splice,hp]\n  · rwa [rightPart_splice,rightPart_splice]\n\ntheorem tail_011_center (left : Int → Bool) (bs : List Bool) (t : Nat) :\n    evol (splice left (word (bs++[false,true,true]))) t 0=\n      evol (splice left (word (bs++[false,true]))) t 0 :=\n  splice_same_center left (tail_011_response bs) t\n\ntheorem tail_101_center (left : Int → Bool) (bs : List Bool) (t : Nat) :\n    evol (splice left (word (bs++[true,false,true]))) t 0=\n      evol (splice left (word (bs++[true,true]))) t 0 :=\n  splice_same_center left (tail_101_response bs) t\n\nend Rule30Submission.Response\n\n/-!\n# An eight-periodic infinite-tail obstruction to OR-only reconstruction\n\nThe two explicit right halves have identical nonconstant head/neighbor OR\nobservations and different head traces. Both full diagonal orbits have period\ndividing eight. A third example has head period two and full-state least\nperiod eight. None is finitely supported: these are not counterexamples\nto the finite-tail conjectures and prove no prize result.\n-/\n\n\n\nnamespace Rule30Submission.Profiles\n\nopen Rule30Submission.Response\n\ndef key (k : Nat) : Nat := if k<4 then k else 4+(k-4)%4\ndef nextKey (i : Nat) : Nat := if i<7 then i+1 else 4\n\ntheorem key_lt (k : Nat) : key k<8 := by\n  unfold key\n  split <;> omega\n\ntheorem key_succ (k : Nat) : key (k+1)=nextKey (key k) := by\n  unfold key nextKey\n  split <;> split <;> split <;> omega\n\ndef profile (which : Bool) (i : Nat) : Nat :=\n  (if which then [45,43,186,166,101,149,86,89]\n   else [42,45,51,170,170,85,170,85]).getD i 0\n\ndef frame (which : Bool) (t k : Nat) : Bool := (profile which (key k)).testBit (t%8)\ndef initial (which : Bool) : State := frame which 0\n\ntheorem profile_step_table : ∀ which : Bool, ∀ t i : Fin 8,\n    (profile which i.val).testBit ((t.val+1)%8)=\n      xor ((profile which i.val).testBit t.val)\n        ((profile which (nextKey i.val)).testBit t.val ||\n         (profile which (nextKey (nextKey i.val))).testBit t.val) := by decide\n\ntheorem frame_step (which : Bool) (t : Nat) : diagonal (frame which t)=frame which (t+1) := by\n  funext k\n  have h := profile_step_table which ⟨t%8,Nat.mod_lt _ (by decide)⟩ ⟨key k,key_lt k⟩\n  simpa only [diagonal,frame,key_succ,show k+2=(k+1)+1 by omega,\n    show (t+1)%8=(t%8+1)%8 by omega] using h.symm\n\ntheorem iterate_frame (which : Bool) : ∀ t, iterate (initial which) t=frame which t\n  | 0 => rfl\n  | t+1 => by rw [iterate,iterate_frame,frame_step]\n\ntheorem full_period_eight (which : Bool) (t : Nat) :\n    iterate (initial which) (t+8)=iterate (initial which) t := by\n  rw [iterate_frame,iterate_frame]\n  funext k\n  simp [frame]\n\ntheorem same_OR_table : ∀ t : Fin 8,\n    ((profile true 0).testBit t.val || (profile true 1).testBit t.val)=\n    ((profile false 0).testBit t.val || (profile false 1).testBit t.val) := by decide\n\ntheorem same_OR (t : Nat) :\n    (iterate (initial true) t 0 || iterate (initial true) t 1)=\n    (iterate (initial false) t 0 || iterate (initial false) t 1) := by\n  simpa only [iterate_frame,frame,key,show 0<4 by decide,show 1<4 by decide,\n    ite_true] using same_OR_table ⟨t%8,Nat.mod_lt _ (by decide)⟩\n\ntheorem OR_nonconstant :\n    (iterate (initial true) 0 0 || iterate (initial true) 0 1)=true ∧\n    (iterate (initial true) 4 0 || iterate (initial true) 4 1)=false := by\n  rw [iterate_frame,iterate_frame]\n  decide\n\ntheorem heads_differ : initial true 0≠initial false 0 := by decide\n\ntheorem tail_OR_different :\n    (iterate (initial true) 2 1 || iterate (initial true) 2 2)≠\n    (iterate (initial false) 2 1 || iterate (initial false) 2 2) := by\n  rw [iterate_frame,iterate_frame]\n  decide\n\ntheorem infinite_true : ¬Rule30ZeroBoundary.FinSupp (initial true) := by\n  rintro ⟨W,hW⟩\n  have h := hW (4*(W+1)+4) (by omega)\n  have hk : key (4*(W+1)+4)=4 := by\n    unfold key\n    rw [ite_eq_right (by omega)]\n    omega\n  change (profile true (key (4*(W+1)+4))).testBit 0=false at h\n  rw [hk] at h\n  contradiction\n\ntheorem infinite_false : ¬Rule30ZeroBoundary.FinSupp (initial false) := by\n  rintro ⟨W,hW⟩\n  have h := hW (4*(W+1)+5) (by omega)\n  have hk : key (4*(W+1)+5)=5 := by\n    unfold key\n    rw [ite_eq_right (by omega)]\n    omega\n  change (profile false (key (4*(W+1)+5))).testBit 0=false at h\n  rw [hk] at h\n  contradiction\n\n/-- A third infinite right half: the head has period two but its neighbor\nand full diagonal state have least period eight. -/\ndef lossProfile (i : Nat) : Nat := [85,87,168,212,172,178,202,43].getD i 0\ndef lossFrame (t k : Nat) : Bool := (lossProfile (key k)).testBit (t%8)\ndef lossInitial : State := lossFrame 0\n\ntheorem loss_step_table : ∀ t i : Fin 8,\n    (lossProfile i.val).testBit ((t.val+1)%8)=\n      xor ((lossProfile i.val).testBit t.val)\n        ((lossProfile (nextKey i.val)).testBit t.val ||\n         (lossProfile (nextKey (nextKey i.val))).testBit t.val) := by decide\n\ntheorem loss_frame_step (t : Nat) : diagonal (lossFrame t)=lossFrame (t+1) := by\n  funext k\n  have h := loss_step_table ⟨t%8,Nat.mod_lt _ (by decide)⟩ ⟨key k,key_lt k⟩\n  simpa only [diagonal,lossFrame,key_succ,show k+2=(k+1)+1 by omega,\n    show (t+1)%8=(t%8+1)%8 by omega] using h.symm\n\ntheorem loss_iterate_frame : ∀ t, iterate lossInitial t=lossFrame t\n  | 0 => rfl\n  | t+1 => by rw [iterate,loss_iterate_frame,loss_frame_step]\n\ntheorem loss_full_period_eight (t : Nat) : iterate lossInitial (t+8)=iterate lossInitial t := by\n  rw [loss_iterate_frame,loss_iterate_frame]\n  funext k\n  simp [lossFrame]\n\ntheorem loss_head_period_two (t : Nat) : iterate lossInitial (t+2) 0=iterate lossInitial t 0 := by\n  have h : ∀ t : Fin 8, (lossProfile 0).testBit ((t.val+2)%8)=(lossProfile 0).testBit t.val := by decide\n  simpa only [loss_iterate_frame,lossFrame,key,show 0<4 by decide,ite_true,\n    show (t+2)%8=(t%8+2)%8 by omega] using h ⟨t%8,Nat.mod_lt _ (by decide)⟩\n\ntheorem loss_neighbor_short_table : ∀ P : Fin 8, 0<P.val → ∃ t : Fin 8,\n    (lossProfile 1).testBit ((t.val+P.val)%8)≠(lossProfile 1).testBit t.val := by decide\n\ntheorem loss_full_period_lower_bound (P : Nat) (hP : 0<P)\n    (hp : ∀ t, iterate lossInitial (t+P)=iterate lossInitial t) : 8≤P := by\n  by_cases hbig : 8≤P\n  · exact hbig\n  · obtain ⟨t,ht⟩ := loss_neighbor_short_table ⟨P,by omega⟩ hP\n    have h := congrFun (hp t.val) 1\n    simp only [loss_iterate_frame,lossFrame,key,show 1<4 by decide,ite_true,\n      Nat.mod_eq_of_lt t.isLt] at h\n    exact False.elim (ht h)\n\ntheorem loss_not_head_period_one : ¬∀ t, iterate lossInitial (t+1) 0=iterate lossInitial t 0 := by\n  intro h\n  have hh := h 0\n  rw [loss_iterate_frame,loss_iterate_frame] at hh\n  contradiction\n\ntheorem loss_infinite : ¬Rule30ZeroBoundary.FinSupp lossInitial := by\n  rintro ⟨W,hW⟩\n  have h := hW (4*(W+1)+7) (by omega)\n  have hk : key (4*(W+1)+7)=7 := by\n    unfold key\n    rw [ite_eq_right (by omega)]\n    omega\n  change (lossProfile (key (4*(W+1)+7))).testBit 0=false at h\n  rw [hk] at h\n  contradiction\n\nend Rule30Submission.Profiles\n",
  "ProjectDir" -> $Rule30PrizeKit, "IncludeInternal" -> True];
rule30KernelCheck = rule30Submission["Rule30Submission.Response.sameResponse_iff_diagonal"]["KernelCheck"];
rule30KernelCheck
```

```wl
responseHeadlines = {"Rule30Submission.Response.sameResponse_iff_diagonal", "Rule30Submission.Response.sameResponse_iff_drv", "Rule30Submission.Response.tail_011_drv", "Rule30Submission.Response.tail_101_drv", "Rule30Submission.Response.feedback_left_equal", "Rule30Submission.Response.tail_011_center", "Rule30Submission.Response.tail_101_center", "Rule30Submission.Response.short_window_not_sameResponse", "Rule30Submission.Response.fixed_driver_counterexample", "Rule30Submission.Profiles.full_period_eight", "Rule30Submission.Profiles.same_OR", "Rule30Submission.Profiles.OR_nonconstant", "Rule30Submission.Profiles.heads_differ", "Rule30Submission.Profiles.infinite_true", "Rule30Submission.Profiles.infinite_false", "Rule30Submission.Profiles.loss_head_period_two", "Rule30Submission.Profiles.loss_full_period_lower_bound", "Rule30Submission.Profiles.loss_infinite"};
Table[<|"Theorem" -> name, "Kind" -> rule30Submission[name]["Kind"],
  "Axioms" -> rule30Submission[name]["Axioms"]|>, {name, responseHeadlines}]
```

Finite-tail normal-form completeness, actual fixed-driver trace rigidity and
the full center-column problem remain open. No new prize essay is submitted
by this build.
