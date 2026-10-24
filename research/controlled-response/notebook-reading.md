Reader export of the evaluated notebook. The reader abbreviates long source and output cells; the complete proof is in the notebook and Rule30ControlledResponseStandalone.lean.

# Controlled responses and finite-support observability limits in Rule 30

Troy Lowry; OpenAI Codex • 2026-10-24

Responses of a right half to every left-boundary input are characterized exactly by two observations of a triangular diagonal map. Terminal rewrites 011 to 01 and 101 to 11 preserve the complete center trace with every common initial left half. Explicit eight-periodic infinite tails show that OR alone need not recover the head and that a period-two head need not detect a full period-eight state. Finite feedback can erase an initial distinction even when the common output is not eventually constant. Finite-tail completeness and the Rule 30 Prize problems remain open.

## Scope and provenance

This is a partial contribution developed by Troy Lowry with OpenAI Codex. It builds on the kit's driven right half in Rule30Ether and whole-line evolution in Rule30Realization. No literature-priority claim is made. The essay is prepared for human review and has not been sent to the prize API.

The terminal rewrites can change a finite row's right edge without changing its center trace. For example, the two rows with black cells only at positions {2,3} and {2}, respectively, have identical center traces at every time. Their left edges agree; this does not refute recovering a left edge from the trace. The general theorem allows every common initial left half and every shared finite prefix before the displayed terminal word.

## Exact response equivalence

Index a right-half state x by 0,1,… for physical positions 1,2,… . Define

Q(x)(k) = x(k) XOR (x(k+1) OR x(k+2)).     F\_b(x)  = (b XOR (x(0) OR x(1))) :: Q(x).

The second formula is exactly one Rule 30 step with left boundary bit b. Two right states have equal head outputs for every boundary-input sequence and every time if and only if, for every n, both the head and the OR of the first two cells of Q^n(x) agree. The infinite response tree is therefore replaced by two observations along one deterministic orbit. The theorem places no finite-support restriction on this equivalence.

For every common finite prefix, terminal 011 followed by zeros can be replaced by 01, and terminal 101 followed by zeros by 11. Both replacements preserve responses to all boundary inputs for all times. A separate induction shows that this equivalence remains sound with actual feedback through the center: if initial left halves, including the center, agree, they agree at every later time. Thus both terminal rewrites preserve the complete center trace in the full Rule 30 system, including when both starting rows are finite.

No converse from a single prescribed driver is proved. In fact, right states 1 and 11 have the same head output forever under the constantly zero driver, but are not universally response equivalent. This driver is not asserted to extend to a finite whole-line orbit. A second example, packed states 42 and 70, agrees through thirteen observations for every driver but is not universally equivalent. Checking only 2W-1 observations is insufficient at W=7.

## A finite actual-feedback counterexample

There is a stronger failure of the converse from one realized input. Let the common initial left half, including the center, be all white, and put black cells at {1} in one row and {1,2} in the other. Their initial right halves 1 and 11 are not universally response equivalent. With the white initial center, one step sends them to 11 and 101. The terminal rewrite above proves these new right halves universally equivalent. The entire left halves still agree, so feedback soundness applies at every subsequent time.

Thus both the complete center traces and complete right-head traces agree forever, although the initial controlled response classes differ. Both starts are finite and nonzero. The kit's finite-configuration version of Jen's period-one result proves that neither common trace is eventually constant. This is an actual whole-line feedback example, without assuming an externally constant input. Their left edges are both position 1, so it does not refute left-edge recovery. No claim about their eventual periodicity is made.

## Why the support and observation hypotheses matter

Write an infinite row from its head toward the right. The two starts

x = 1100(1101)…     y = 0110(01)…

use parenthesized blocks repeated forever. Both complete Q orbits have period dividing eight. Their head traces differ, but the OR of the first two cells is the same nonconstant sequence at every time. At time two, the next OR, of cells one and two, differs. The common OR alone cannot recover the head or the next OR. These states are not universally response equivalent, because that relation observes the head as well.

A third start, 1100(0001)…, has a head trace of least period two, whereas its complete Q orbit has least period eight. All three starts are proved to have infinite support. A power-of-two orbit period cannot replace finite support in a proposed head-period detection theorem. No finite-tail conjecture is refuted or proved by these examples.

The proofs use explicit temporal profile tables, verify their scalar update at every depth, and then identify all iterates by induction. The finite search that found the tables is not a proof premise. No part of this essay excludes an eventual center period or proves a Rule 30 Prize problem.

## Independent finite controls

The first calculation compares terminal rewrites in 104 complete Rule 30 experiments with random common left halves and prefixes. The second compares all three profile tables with built-in Rule 30 on finite causal cones. The third checks eight actual-feedback examples, including the all-white left half, at both the center and the right head through time 128. These controls do not replace the unbounded kernel proofs.

```wl
In[1]:=
(* Independent finite samples using the built-in Rule 30 evolution.
   Unbounded statements and feedback soundness are proved in Lean. *)
ClearAll[controlledResponseReport];
controlledResponseReport[] := BlockRandom[
  SeedRandom[20261024];
  Module[{cases},
    cases = Flatten[Table[Module[{left, prefix, old, new, ca, cb, center = 8},
      left = RandomInteger[1, 9];
      prefix = RandomInteger[1, n];
      {old, new} = If[rule == 0, {{0, 1, 1}, {0, 1, 0}}, {{1, 0, 1}, {1, 1, 0}}];
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
  tables = {{45, 43, 186, 166, 101, 149, 86, 89},
    {42, 45, 51, 170, 170, 85, 170, 85}, {85, 87, 168, 212, 172, 178, 202, 43}};
  counts = Table[Module[{profile, n, initial, ca, checks},
    profile[k_] := table[[If[k < 4, k + 1, 5 + Mod[k - 4, 4]]]];
    n = window + 2 * h + 2;
    initial = Table[BitAnd[profile[k], 1], {k, 0, n - 1}];
    ca = CellularAutomaton[30, Join[ConstantArray[0, h + 1], initial, ConstantArray[0, h + 1]], h];
    checks = Flatten@Table[
      ca[[t + 1, h + 2 + k + t]] == BitAnd[BitShiftRight[profile[k], Mod[t, 8]], 1],
      {t, 0, h}, {k, 0, window - 1}];
    <|"ScalarCellsCompared" -> Length[checks], "AllPassed" -> And@@checks|>
  ], {table, tables}];
  <|"FiniteControlsOnly" -> True, "FullProblemClaim" -> False,
    "BuiltinRule30Cones" -> Length[counts], "Cases" -> counts,
    "AllPassed" -> And@@Lookup[counts, "AllPassed"]|>
];

ClearAll[profileCounterDiagram];
profileCounterDiagram[] := Module[{tables, labels},
  tables = {{45, 43, 186, 166, 101, 149, 86, 89},
    {42, 45, 51, 170, 170, 85, 170, 85}, {85, 87, 168, 212, 172, 178, 202, 43}};
  labels = {"First OR example", "Second OR example", "Head period 2; state period 8"};
  GraphicsRow[Table[ArrayPlot[
    Table[BitAnd[BitShiftRight[tables[[j, If[k < 4, k + 1, 5 + Mod[k - 4, 4]]]], t], 1],
      {t, 0, 7}, {k, 0, 11}], ColorRules -> {0 -> White, 1 -> Black},
    Frame -> True, FrameTicks -> None, Mesh -> All, MeshStyle -> LightGray,
    PlotLabel -> Style[labels[[j]], 12],
    (* ArrayPlot orders these as {{bottom,top},{left,right}}. *)
    FrameLabel -> {{"position 0 through 11", None}, {"time 0 through 7 from top", None}},
    ImageSize -> 320], {j, 3}], ImageSize -> 1050]
];

(* Built-in full Rule 30 controls for the actual-feedback collision.
   Finite observations here accompany, and do not replace, the Lean proof. *)
ClearAll[feedbackErasureReport];
feedbackErasureReport[] := BlockRandom[
  SeedRandom[2026102406];
  Module[{cases},
    cases = Table[Module[{left, a, b, ca, cb, ha, hb, center = 8},
      left = If[sample == 1, ConstantArray[0, 9], Append[RandomInteger[1, 8], 0]];
      a = Join[left, {1, 0}]; b = Join[left, {1, 1}];
      ca = Flatten@CellularAutomaton[30, {a, 0}, {128, {{center}}}];
      cb = Flatten@CellularAutomaton[30, {b, 0}, {128, {{center}}}];
      ha = Flatten@CellularAutomaton[30, {a, 0}, {128, {{center + 1}}}];
      hb = Flatten@CellularAutomaton[30, {b, 0}, {128, {{center + 1}}}];
      <|"AllWhiteLeft" -> (sample == 1), "Horizon" -> 128,
        "ObservationCount" -> Length[ca], "SameCenterTracePrefix" -> SameQ[ca, cb],
        "SameRightHeadTracePrefix" -> SameQ[ha, hb],
        "CenterPrefixNonconstant" -> (Length[DeleteDuplicates[ca]] == 2),
        "HeadPrefixNonconstant" -> (Length[DeleteDuplicates[ha]] == 2)|>
    ], {sample, 1, 8}];
    <|"FiniteSamplesOnly" -> True, "UnboundedProofReplaced" -> False,
      "FullProblemClaim" -> False, "CaseCount" -> Length[cases],
      "AllPassed" -> And@@(And@@Lookup[#, {"SameCenterTracePrefix",
        "SameRightHeadTracePrefix", "CenterPrefixNonconstant", "HeadPrefixNonconstant"}]& /@ cases),
      "Cases" -> cases|>
  ]
];

{controlledResponseReport[], profileCounterReport[], feedbackErasureReport[]}

Out[1]=  {<|"FiniteSamplesOnly" -> True, "UnboundedProofReplaced" -> False, "FullProblemClaim" -> False, "CaseCount" -> 104, "AllPassed" -> True, "Cases" -> {<|"PrefixLength" -> 0, "Rewrite" -> "011->01", "Horizon" -> 128, "ObservationCount" -> 129, "SameCe ... HeadPrefixNonconstant" -> True|>, <|"AllWhiteLeft" -> False, "Horizon" -> 128, "ObservationCount" -> 129, "SameCenterTracePrefix" -> True, "SameRightHeadTracePrefix" -> True, "CenterPrefixNonconstant" -> True, "HeadPrefixNonconstant" -> True|>}|>}
```

The diagram shows eight times, from top to bottom, and the first twelve cells of each infinite row. Black squares are black cells. The right tail repeats from position four. The last panel's first column alternates while later columns require eight times to repeat; the all-time claims are proved below.

```wl
In[2]:=  profileCounterDiagram[]

Out[2]=  ![cell image](attachment://content-8cvqo)
```

## Exact embedded proof and full kernel replay

The source below contains all three complete catalog modules, with only imports, module/export wrappers and namespace names adapted for a standalone file. It imports only official core modules and uses no additional axioms or native decision procedures. A passing partial check does not establish an official prize target.

```wl
In[3]:=
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit = Environment["RULE30PRIZE_KIT"];

In[4]:=
rule30Submission = LeanImportString["import Ruliology.CellularAutomata.Rule30Ether
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
  x 0=y 0 ∧ (x 0 || x 1)=(y 0 || y 1 ... 0 → evol (splice left (word [true])) 1 p =
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
",
  "ProjectDir" -> $Rule30PrizeKit, "IncludeInternal" -> True];
rule30KernelCheck = rule30Submission["Rule30Submission.Response.sameResponse_iff_diagonal"]["KernelCheck"];
rule30KernelCheck

Out[4]=
Success["KernelChecked", Association["MessageTemplate" ->
   "The kernel accepts all `1` declarations of `2`.", "MessageParameters" ->
   {238, "LeanLinkTmp33396275289253062788x733523"},
  "Module" -> "LeanLinkTmp33396275289253062788x733523", "Declarations" -> 238]]

In[5]:=
responseHeadlines = {"Rule30Submission.Response.sameResponse_iff_diagonal", "Rule30Submission.Response.sameResponse_iff_drv", "Rule30Submission.Response.tail_011_drv", "Rule30Submission.Response.tail_101_drv", "Rule30Submission.Response.feedback_left_equal", "Rule30Submission.Response.tail_011_center", "Rule30Submission.Response.tail_101_center", "Rule30Submission.Response.short_window_not_sameResponse", "Rule30Submission.Response.fixed_driver_counterexample", "Rule30Submission.Profiles.full_period_eight", "Rule30Submission.Profiles.same_OR", "Rule30Submission.Profiles.OR_nonconstant", "Rule30Submission.Profiles.heads_differ", "Rule30Submission.Profiles.infinite_true", "Rule30Submission.Profiles.infinite_false", "Rule30Submission.Profiles.loss_head_period_two", "Rule30Submission.Profiles.loss_full_period_lower_bound", "Rule30Submission.Profiles.loss_infinite", "Rule30Submission.Feedback.white_step_erases_distinction", "Rule30Submission.Feedback.same_left_forever", "Rule30Submission.Feedback.finite_feedback_counterexample"};
Table[<|"Theorem" -> name, "Kind" -> rule30Submission[name]["Kind"],
  "Axioms" -> rule30Submission[name]["Axioms"]|>, {name, responseHeadlines}]

Out[5]=  {<|"Theorem" -> "Rule30Submission.Response.sameResponse_iff_diagonal", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "propext"}|>, <|"Theorem" -> "Rule30Submission.Response.sameResponse_iff_drv", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "p ... Feedback.same_left_forever", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "propext"}|>, <|"Theorem" -> "Rule30Submission.Feedback.finite_feedback_counterexample", "Kind" -> "theorem", "Axioms" -> {"Classical.choice", "Quot.sound", "propext"}|>}
```

Finite-tail normal-form completeness, actual fixed-driver trace rigidity and the full center-column problem remain open. No new prize essay is submitted by this build.
