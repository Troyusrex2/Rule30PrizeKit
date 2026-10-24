Reader export of the evaluated notebook. The reader abbreviates long source and output cells; the complete proof is in the notebook and Rule30ControlledResponseStandalone.lean.

# Controlled responses and finite-support observability limits in Rule 30

Troy Lowry; OpenAI Codex • 2026-10-24

Responses of a right half to every left-boundary input are characterized exactly by two observations of a triangular diagonal map. Terminal rewrites 011 to 01 and 101 to 11 preserve the complete center trace with every common initial left half. Explicit eight-periodic infinite tails show that OR alone need not recover the head and that a period-two head need not detect a full period-eight state. Finite feedback can erase an initial distinction even when the common output is not eventually constant. A checked finite-profile certificate also proves head-period detection for every finite width at full clock sixteen. Finite-tail completeness and the Rule 30 Prize problems remain open.

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

## A local clock obstruction with explicit hypotheses

Let five temporal columns a,b,c,d,e obey the triangular update, so the next a is a XOR (b OR c), the next b is b XOR (c OR d), and the next c is c XOR (d OR e). Put H=2n. Assume a has period 2H, b reverses color after H, and c and d each have period H. Then a OR b cannot have period H. Any additional predecessor whose temporal difference is a OR b cannot have period H either. There is a direct application to columns of the actual Q orbit with every clock assumption retained.

The proof supposes the OR has period H. Since b reverses after H, the OR would have to be constantly black. Define K(t)=a(t) XOR a(t+H). The local updates force d(t) to be at most c(t), and K XOR b would alternate each step. It would then be both H-periodic and color-reversing after the even number H of steps, which is impossible.

This protects the neighborhood of a clock onset. It does not prove arbitrary prefix propagation, a finite-tail period-detection theorem, or center-column nonperiodicity. In particular, the even half-clock and full-clock premises must not be dropped. No literature-priority claim is made.

## A fixed-clock theorem covering every finite width

There is now a positive finite-tail result at full clock sixteen. For every finitely supported x with Q^16(x)=x, any eventual head period H is a period of the entire state: Q^H(x)=x. The spatial width, the transient, and H are arbitrary. The full-clock assumption is retained explicitly. This is a triangular-orbit theorem, rather than a statement about a vertical center.

The proof checks a pool of 68 pairs of temporal profiles. Every pair in the pool has either no consistent predecessor column at this full clock, or both possible predecessors are again in the pool. Starting from the finite zero tail, induction covers every finite spatial width. A second check propagates a head period through every pair. All head-clock residues modulo sixteen are checked, and periodicity reduces every natural H to its residue. A purely periodic orbit turns any eventual head period into a period from time zero, so no transient bound is needed.

The finite search that generated the pool is not trusted. The generic Lean checker proves the soundness of the closure and detection checks; the concrete checks are evaluated by the kernel. This establishes neither an arbitrary-full-clock induction nor a center-column prize result. The earlier infinite-tail period-loss example satisfies the full-clock bound and illustrates why the finite-support premise matters.

## An unbounded clock statement for the known terminal rewrites

The two terminal rewrites preserve more than the observed response. Behind every shared finite prefix, their complete Q-state orbits have exactly the same equality relations: Q``^s(x) = Q``t(x) if and only if Q``^s(y) = Q``t(y), for every s and t. In particular Q^H(x)=x if and only if Q^H(y)=y, for every H. There is no full-clock bound in this statement.

The proof uses the two tails [a,not a,1] and [a,1]. One Q step switches a and updates both prefixes equally. An indexed relation records the prefix length. Inserting or deleting the terminal cell reconstructs either linked state from the other, and the relation survives every Q step. The same conclusion follows for any finite chain of the sound rewrites.

Thus these known response collisions themselves preserve the full temporal clock. Completeness is still missing: the argument does not establish that every finite response collision is generated by these rewrites. No arbitrary head-period detection theorem or vertical-center result follows here.

## Independent finite controls

The first calculation compares terminal rewrites in 104 complete Rule 30 experiments with random common left halves and prefixes. The second compares all three profile tables with built-in Rule 30 on finite causal cones. The third checks eight actual-feedback examples, including the all-white left half, at both the center and the right head through time 128. The fourth checks 192 qualifying clock cases among 512 finite starts and compares ten whole-row Q evolutions with built-in Rule 30 on slanted causal cones. The fifth independently checks eight further cones for finite tails whose widths extend well beyond the clock bound. The sixth checks both sides of the terminal correspondence against sixteen built-in Rule 30 cones, comparing 26,264 scalar cells. Separate Python controls check 1,122,302 state pairs, including 256 wide prefixes. These controls do not replace the unbounded kernel proofs.

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

(* Finite controls, independent of the unbounded Lean proof. *)
ClearAll[clockMaskReport];
clockMaskReport[] := Module[{q, orbit, cases = {}, caChecks = {}, row, p, h, profiles,
    aa, bb, cc, dd, ss, prev, w, horizon = 32, initial, ca, iter, samples},
  q[x_] := BitXor[x, BitOr[BitShiftRight[x, 1], BitShiftRight[x, 2]]];
  Do[
    orbit = {a}; row = q[a];
    While[row != a, AppendTo[orbit, row]; row = q[row]];
    p = Length[orbit];
    If[p >= 4,
      h = p / 2; w = IntegerLength[a, 2 ... files[[k]]];
          AppendTo[cases, <|"Word" -> a, "Column" -> k, "Clock" -> p,
            "ORNonconstant" -> (Length[DeleteDuplicates[ss]] == 2),
            "ORNotHalfPeriodic" -> (RotateLeft[ss, h] =!= ss),
            "PredecessorNotHalfPeriodicWhenPresent" -> prev|>]
        ], {k, 0, w - 1}]
    ], {a, 0, 511}];
  samples = {4, 7, 8, 16, 32, 33, 64, 160, 528, 529};
  Do[
    w = IntegerLength[a, 2];
    initial = Join[ConstantArray[0, horizon + 1], Table[BitAnd[BitShiftRight[a, k], 1], {k, 0, w - 1}],
      ConstantArray[0, 3 * horizon + 1]];
    ca = CellularAutomaton[30, initial, horizon]; iter = NestList[q, a, horizon];
    AppendTo[caChecks, And@@Flatten@Table[
      ca[[t + 1, horizon + 2 + k + t]] == BitAnd[BitShiftRight[iter[[t + 1]], k], 1],
      {t, 0, horizon}, {k, 0, w - 1}]], {a, samples}];
  <|"FiniteControlsOnly" -> True, "LeanVerifiedByThisCalculation" -> False,
    "FullProblemClaim" -> False, "InitialWordsChecked" -> 512,
    "OnsetCasesChecked" -> Length[cases], "BuiltinRule30Cones" -> Length[samples],
    "AllPassed" -> (Length[cases] > 0 && And@@caChecks &&
      And@@Flatten[Lookup[cases, {"ORNonconstant", "ORNotHalfPeriodic",
        "PredecessorNotHalfPeriodicWhenPresent"}]]), "Cases" -> cases|>
];

(* Finite controls using independent built-in Rule 30 causal cones. *)
ClearAll[finiteClock16Report];
finiteClock16SampleWords = {1071292029505993517027974728227441735014801995855195223534253, 3148244321913096809142, 1650586719047173699865498955, 9514984618039732540388573129663300909218310819, 2043327387821185144477796036200412244824985496244802899, 5230918112822233969863157852673055346751962870386695427400, 15011998757901638, 31178701596392595588345276431280704419326560916806};
finiteClock16Report[] := Module[{words = finiteClock16SampleWords, q, h = 32, cases},
  q[x_] := BitXor[x, BitOr[BitShiftRight[x, 1], BitShiftRight[x, 2]]];
  cases = Table[Module[{w = IntegerLength[a, 2], initial, ca, iter, checks, head, hs},
    initial = Join[ConstantArray[0, h + 1], Reverse[IntegerDigits[a, 2]], ConstantArray[0, 3 * h + 1]];
    ca = CellularAutomaton[30, initial, h];iter = NestList[q, a, h];
    checks = Flatten@Table[ca[[t + 1, h + 2 + k + t]] == BitAnd[BitShiftRight[iter[[t + 1]], k], 1],
      {t, 0, h}, {k, 0, w - 1}];
    head = BitAnd[#, 1]& /@ Take[iter, 16];
    hs = Select[Range[0, 15], RotateLeft[head, #] === head&];
    <|"Width" -> w, "FullClockReturns" -> (iter[[17]] == a), "ScalarCellsCompared" -> Length[checks],
      "BuiltinConeMatchesQ" -> And@@checks,
      "HeadClocksDetected" -> And@@Table[iter[[H + 1]] == a, {H, hs}]|>
  ], {a, words}];
  <|"FiniteControlsOnly" -> True, "LeanVerifiedByThisCalculation" -> False,
    "FullProblemClaim" -> False, "BuiltinRule30Cones" -> Length[cases],
    "ScalarCellsCompared" -> Total[Lookup[cases, "ScalarCellsCompared"]],
    "AllPassed" -> And@@Flatten[Lookup[cases, {"FullClockReturns", "BuiltinConeMatchesQ", "HeadClocksDetected"}]],
    "Cases" -> cases|>
];

(* Independent built-in Rule 30 cones for both tails. *)
ClearAll[terminalClockReport];
terminalClockReport[] := Module[{q, h = 48, cases, samples},
  q[x_] := BitXor[x, BitOr[BitShiftRight[x, 1], BitShiftRight[x, 2]]];
  samples = {{0, 0, 0}, {0, 0, 1}, {1, 1, 0}, {7, 93, 1}, {16, 52311, 0},
    {32, 3687745881, 1}, {64, 17644052093809732657, 0},
    {128, 270201093290129833730702342604831702973, 1}};
  cases = Table[Module[{n = s[[1]], prefix = s[[2]], a = s[[3]], short, long, ss, ll, cone, cells = 0, ok = True},
    short = prefix + 2 ^ n * (a + 2);long = prefix + 2 ^ n * (a + 2 * (1 - a) + 4);
    ss = NestList[q, short, h];ll = NestList[q, long, h];
    Do[Module[{w = IntegerLength[row, 2], initial, ca, it},
      initial = Join[ConstantArray[0, h + 1], Reverse[IntegerDigits[row, 2]], ConstantArray[0, 3 * h + 1]];
      ca = CellularAutomaton[30, initial, h];it = NestList[q, row, h];
      cells += (h + 1) * w;
      ok = ok && And@@Flatten@Table[
        ca[[t + 1, h + 2 + k + t]] == BitAnd[BitShiftRight[it[[t + 1]], k], 1],
        {t, 0, h}, {k, 0, w - 1}]
    ], {row, {short, long}}];
    <|"PrefixLength" -> n, "BuiltinConesMatch" -> ok, "ScalarCellsCompared" -> cells,
      "FullStateReturnTimesAgree" -> (((# == short)& /@ ss) === ((# == long)& /@ ll)),
      "OrbitEqualityRelationsAgree" -> And@@Flatten@Table[
        (ss[[i]] == ss[[j]]) === (ll[[i]] == ll[[j]]), {i, h + 1}, {j, h + 1}]|>
  ], {s, samples}];
  <|"FiniteControlsOnly" -> True, "LeanVerifiedByThisCalculation" -> False, "FullProblemClaim" -> False,
    "Cases" -> cases, "BuiltinRule30Cones" -> 2 * Length[cases],
    "ScalarCellsCompared" -> Total[Lookup[cases, "ScalarCellsCompared"]],
    "AllPassed" -> And@@Flatten[Lookup[cases,
      {"BuiltinConesMatch", "FullStateReturnTimesAgree", "OrbitEqualityRelationsAgree"}]]|>
];

{controlledResponseReport[], profileCounterReport[], feedbackErasureReport[], clockMaskReport[], finiteClock16Report[], terminalClockReport[]}

Out[1]=  {<|"FiniteSamplesOnly" -> True, "UnboundedProofReplaced" -> False, "FullProblemClaim" -> False, "CaseCount" -> 104, "AllPassed" -> True, "Cases" -> {<|"PrefixLength" -> 0, "Rewrite" -> "011->01", "Horizon" -> 128, "ObservationCount" -> 129, "SameCe ... <|"PrefixLength" -> 128, "BuiltinConesMatch" -> True, "ScalarCellsCompared" -> 12789, "FullStateReturnTimesAgree" -> True, "OrbitEqualityRelationsAgree" -> True|>}, "BuiltinRule30Cones" -> 16, "ScalarCellsCompared" -> 26264, "AllPassed" -> True|>}
```

The diagram shows eight times, from top to bottom, and the first twelve cells of each infinite row. Black squares are black cells. The right tail repeats from position four. The last panel's first column alternates while later columns require eight times to repeat; the all-time claims are proved below.

```wl
In[2]:=  profileCounterDiagram[]

Out[2]=  ![cell image](attachment://content-2nq8b)
```

## Exact embedded proof and full kernel replay

The source below contains all seven complete catalog modules, with only imports, module/export wrappers and namespace names adapted for a standalone file. It imports only official core modules and uses no additional axioms or native decision procedures. A passing partial check does not establish an official prize target.

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
  x 0=y 0 ∧ (x 0 || x 1)=(y 0 || y 1 ...  : Nat) (a : Bool) (x : State) :
    deflate (n+1) (prepend a x)=prepend a (deflate n x) := by
  funext k
  cases k with
  | zero => simp [deflate,prepend]
  | succ k => simp [deflate,prepend,Nat.succ_sub_succ_eq_sub]

theorem linked_inflate {n : Nat} {x y : State} (h : Linked n x y) : x=inflate n y := by
  induction h with
  | base a => funext k; simp [inflate,word]
  | cons a h ih => rw [inflate_prepend,← ih]

theorem linked_deflate {n : Nat} {x y : State} (h : Linked n x y) : y=deflate n x := by
  induction h with
  | base a => funext k; simp [deflate,word]
  | cons a h ih => rw [deflate_prepend,← ih]

theorem linked_response {n : Nat} {x y : State} (h : Linked n x y) : SameResponse x y := by
  induction h with
  | base a =>
      cases a with
      | false => exact tail_011_response []
      | true => exact tail_101_response []
  | cons a h ih => exact sameResponse_prepend ih a

/-- One full triangular step preserves the same indexed correspondence. -/
theorem linked_diagonal {n : Nat} {x y : State} (h : Linked n x y) :
    Linked n (diagonal x) (diagonal y) := by
  induction h with
  | base a =>
      cases a with
      | false =>
          change Linked 0 (diagonal (word [false,true,true])) (diagonal (word [false,true]))
          rw [diagonal_011,diagonal_01]
          exact Linked.base true
      | true =>
          change Linked 0 (diagonal (word [true,false,true])) (diagonal (word [true,true]))
          rw [diagonal_101,diagonal_11]
          exact Linked.base false
  | cons a h ih =>
      have hor := (sameResponse_observe (linked_response h)).2
      rw [diagonal_prepend,diagonal_prepend]
      unfold step
      rw [hor]
      exact Linked.cons _ ih

theorem linked_iterate {n : Nat} {x y : State} (h : Linked n x y) :
    ∀ t, Linked n (iterate x t) (iterate y t)
  | 0 => h
  | t+1 => linked_diagonal (linked_iterate h t)

/-- The two full-state orbits have exactly the same equality relations at all times. -/
theorem iterate_equal_iff {n : Nat} {x y : State} (h : Linked n x y) (s t : Nat) :
    iterate x s=iterate x t ↔ iterate y s=iterate y t := by
  constructor
  · intro he
    calc
      iterate y s=deflate n (iterate x s) := linked_deflate (linked_iterate h s)
      _=deflate n (iterate x t) := congrArg (deflate n) he
      _=iterate y t := (linked_deflate (linked_iterate h t)).symm
  · intro he
    calc
      iterate x s=inflate n (iterate y s) := linked_inflate (linked_iterate h s)
      _=inflate n (iterate y t) := congrArg (inflate n) he
      _=iterate x t := (linked_inflate (linked_iterate h t)).symm

theorem return_iff {n : Nat} {x y : State} (h : Linked n x y) (H : Nat) :
    iterate x H=x ↔ iterate y H=y := by
  simpa only [iterate] using iterate_equal_iff h H 0

theorem linked_prefix (bs : List Bool) (a : Bool) :
    Linked bs.length (word (bs++[a,!a,true])) (word (bs++[a,true])) := by
  induction bs with
  | nil => exact Linked.base a
  | cons b bs ih =>
      simpa only [List.cons_append,word_cons,List.length_cons] using Linked.cons b ih

/-- A terminal 011 -> 01 rewrite preserves every full-state return time. -/
theorem tail_011_return_iff (bs : List Bool) (H : Nat) :
    iterate (word (bs++[false,true,true])) H=word (bs++[false,true,true]) ↔
      iterate (word (bs++[false,true])) H=word (bs++[false,true]) :=
  return_iff (linked_prefix bs false) H

/-- A terminal 101 -> 11 rewrite preserves every full-state return time. -/
theorem tail_101_return_iff (bs : List Bool) (H : Nat) :
    iterate (word (bs++[true,false,true])) H=word (bs++[true,false,true]) ↔
      iterate (word (bs++[true,true])) H=word (bs++[true,true]) :=
  return_iff (linked_prefix bs true) H

/-- Repeated sound terminal rewrites also preserve every full-state return time. -/
inductive RewriteEq : State → State → Prop
  | refl (x : State) : RewriteEq x x
  | linked {n : Nat} {x y : State} (h : Linked n x y) : RewriteEq x y
  | symm {x y : State} (h : RewriteEq x y) : RewriteEq y x
  | trans {x y z : State} (h : RewriteEq x y) (g : RewriteEq y z) : RewriteEq x z

theorem rewrite_response {x y : State} (h : RewriteEq x y) : SameResponse x y := by
  induction h with
  | refl x => exact sameResponse_refl x
  | linked h => exact linked_response h
  | symm h ih => exact sameResponse_symm ih
  | trans h g ih ig => exact sameResponse_trans ih ig

theorem rewrite_equal_iff {x y : State} (h : RewriteEq x y) (s t : Nat) :
    iterate x s=iterate x t ↔ iterate y s=iterate y t := by
  induction h with
  | refl x => rfl
  | linked h => exact iterate_equal_iff h s t
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

theorem rewrite_return_iff {x y : State} (h : RewriteEq x y) (H : Nat) :
    iterate x H=x ↔ iterate y H=y := by
  simpa only [iterate] using rewrite_equal_iff h H 0

end Rule30Submission.TerminalClock
",
  "ProjectDir" -> $Rule30PrizeKit, "IncludeInternal" -> True];
rule30KernelCheck = rule30Submission["Rule30Submission.Response.sameResponse_iff_diagonal"]["KernelCheck"];
rule30KernelCheck

Out[4]=
Success["KernelChecked", Association["MessageTemplate" ->
   "The kernel accepts all `1` declarations of `2`.", "MessageParameters" ->
   {394, "LeanLinkTmp33396308588221109786x912428"},
  "Module" -> "LeanLinkTmp33396308588221109786x912428", "Declarations" -> 394]]

In[5]:=
responseHeadlines = {"Rule30Submission.Response.sameResponse_iff_diagonal", "Rule30Submission.Response.sameResponse_iff_drv", "Rule30Submission.Response.tail_011_drv", "Rule30Submission.Response.tail_101_drv", "Rule30Submission.Response.feedback_left_equal", "Rule30Submission.Response.tail_011_center", "Rule30Submission.Response.tail_101_center", "Rule30Submission.Response.short_window_not_sameResponse", "Rule30Submission.Response.fixed_driver_counterexample", "Rule30Submission.Profiles.full_period_eight", "Rule30Submission.Profiles.same_OR", "Rule30Submission.Profiles.OR_nonconstant", "Rule30Submission.Profiles.heads_differ", "Rule30Submission.Profiles.infinite_true", "Rule30Submission.Profiles.infinite_false", "Rule30Submission.Profiles.loss_head_period_two", "Rule30Submission.Profiles.loss_full_period_lower_bound", "Rule30Submission.Profiles.loss_infinite", "Rule30Submission.Feedback.white_step_erases_distinction", "Rule30Submission.Feedback.same_left_forever", "Rule30Submission.Feedback.finite_feedback_counterexample", "Rule30Submission.Clocks.no_constant_OR_at_onset", "Rule30Submission.Clocks.OR_not_half_period", "Rule30Submission.Clocks.predecessor_not_half_period", "Rule30Submission.FiniteClockCertificate.finite_family_clock_detected", "Rule30Submission.FiniteClockCertificate.finite_state_eventual_clock_detected", "Rule30Submission.FiniteClockSixteen.eventual_period_detected", "Rule30Submission.FiniteClockSixteen.period_loss_requires_infinite_tail", "Rule30Submission.TerminalClock.iterate_equal_iff", "Rule30Submission.TerminalClock.tail_011_return_iff", "Rule30Submission.TerminalClock.tail_101_return_iff", "Rule30Submission.TerminalClock.rewrite_return_iff"};
Table[<|"Theorem" -> name, "Kind" -> rule30Submission[name]["Kind"],
  "Axioms" -> rule30Submission[name]["Axioms"]|>, {name, responseHeadlines}]

Out[5]=  {<|"Theorem" -> "Rule30Submission.Response.sameResponse_iff_diagonal", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "propext"}|>, <|"Theorem" -> "Rule30Submission.Response.sameResponse_iff_drv", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "p ... > "Rule30Submission.TerminalClock.tail_101_return_iff", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "propext"}|>, <|"Theorem" -> "Rule30Submission.TerminalClock.rewrite_return_iff", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "propext"}|>}
```

Finite-tail normal-form completeness, actual fixed-driver trace rigidity and the full center-column problem remain open. No new prize essay is submitted by this build.
