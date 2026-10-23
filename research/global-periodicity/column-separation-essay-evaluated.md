# Distinguishing every pair of Rule 30 spatial columns

Troy Lowry; OpenAI Codex • 2026-10-23

Every two distinct spatial columns p and q of the single-seed Rule 30 pattern differ by time max(abs(p),abs(q))+18. The mirror case is proved with 20-bit edge windows, certified periods and all 256 phase classes. This is injectivity of complete traces starting at time zero. It does not prove temporal nonperiodicity, exclude eventual equality, or solve a prize problem.

## The statement

For every pair of integers p != q there is a natural time t with

t <= max(abs(p), abs(q)) + 18

at which the cells in columns p and q differ. This covers arbitrarily large positions. The statement concerns complete traces beginning at time zero. It does not exclude eventual equality of two columns and does not answer whether the center column becomes periodic. No literature-first claim is made.

```wl
In[1]:=
ArrayPlot[CellularAutomaton[30, {{1}, 0}, {64, {-64, 64}}], Frame -> True,
  PlotLabel -> "Rule 30 from one black cell"]

Out[1]=
\!\(\*GraphicsBox[RasterBox[CompressedData["«1231»"], {{0, 0}, {129, 65}}, {0, 1}],
 Frame -> True, FrameLabel -> {None, None}, FrameTicks -> {{None, None}, {None, None}},
 GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]],
 Method -> {"GridLines ... " -> {"ratio" -> 2},
       "Droplines" -> {"freeformCursorMode" -> True, "placement" -> {"x" -> "All",
           "y" -> "None"}}}}, "DefaultPlotStyle" -> Automatic},
 PlotLabel -> FormBox["\"Rule 30 from one black cell\"", TraditionalForm]]\)
```

## Why a finite check proves an unbounded family

A column at position p is white before time abs(p), then black at that time. Thus different distances from the seed have different traces. The remaining case consists of the mirror columns -m and m.

Track the first 20 cells behind each moving edge. The right window returns to its initial state after 256 steps. The left window enters a four-step cycle after time 20. These are exact finite-state equalities, checked by Lean's ordinary kernel. Induction extends the cycles to all future times. The 256 possible phases each have a witness among offsets 0 through 18. Small initial exceptions are checked separately. The window bits are proved equal to the official cellwise diagonals, so this proves the mirror result for every m>0.

## Independent Wolfram computation

The following built-in cellular automaton computation independently checks the finite cycles, all 256 phases and 512 sample mirror pairs. These samples are not the justification for the all-position quantifier; the Lean proof below is.

```wl
In[2]:=
ClearAll[columnFrontReport];
columnFrontReport[] := Module[{grid, left, right, lags, residues},
  grid = CellularAutomaton[30, {{1}, 0}, {530, {-530, 530}}];
  left[t_] := Sum[grid[[t + 1, 531 - t + j]] 2 ^ j, {j, 0, 19}];
  right[t_] := Sum[grid[[t + 1, 531 + t - j]] 2 ^ j, {j, 0, 19}];
  lags = Table[FirstPosition[Table[
    Unequal[grid[[m + j + 1, 531 - m]], grid[[m + j + 1, 531 + m]]], {j, 0, 18}], True,
    Missing["NoWitness"]], {m, 1, 512}];
  residues = Table[AnyTrue[Range[0, 18], Function[j,
    BitGet[left[20 + Mod[r + j, 4]], j] != BitGet[right[Mod[r + j, 256]], j]]], {r, 0, 255}];
  <|"engineVersion" -> $VersionNumber, "finiteCrosschecksOnly" -> True,
    "gridDimensions" -> Dimensions[grid], "frontWidth" -> 20,
    "rightCycleCloses" -> SameQ[right[256], right[0]],
    "leftCycleCloses" -> SameQ[left[24], left[20]],
    "leftCycle" -> Table[left[t], {t, 20, 23}],
    "all256ResiduesSeparated" -> And@@residues,
    "all512SampleMirrorPairsSeparated" -> FreeQ[lags, _Missing],
    "exampleM256Lag" -> First[lags[[256]]] - 1|>
];

columnFrontReport[]

Out[2]=  <|"engineVersion" -> 15., "finiteCrosschecksOnly" -> True, "gridDimensions" -> {531, 1061}, "frontWidth" -> 20, "rightCycleCloses" -> True, "leftCycleCloses" -> True, "leftCycle" -> {124691, 291707, 866835, 759419}, "all256ResiduesSeparated" -> True, "all512SampleMirrorPairsSeparated" -> True, "exampleM256Lag" -> 18|>
```

## The complete formal proof

This self-contained source carries the proof; it does not rely on an unmerged research module being installed in the reference kit. The proof bodies match the catalog contribution, with namespace and module wrappers adapted. The underlying catalog diagonal theorems are imported unchanged.

```wl
In[3]:=
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit = Environment["RULE30PRIZE_KIT"];

In[4]:=
rule30Submission = LeanImportString["import Rule30PrizeKit

import Ruliology.CellularAutomata.Rule30Diagonals
import Ruliology.CellularAutomata.Rule30Prize

/-!
# Pairwise distinct complete column traces of the single-seed pattern

For every pair of integers p != q, an observation at time at most
max(|p|,|q|)+18 distinguishes their columns. First arrival distinguishes
different distances from the seed. Mirror columns -m and m differ by time
m+18, using certified 20-bit edge windows: the left window is 4-periodic
after time 20 and the right window is 256-periodic from the start. Checking
all 256 phase classes gives the uniform bound for arbitrarily large m.

This concerns complete traces starting at time zero. It does not exclude
eventual equality, prove temporal nonperiodicity, or solve a prize problem.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Ruliology.CellularAutomata

namespace Rule30Submission

open Rule30Jen Rule30Diagonals

def step (left : Bool) (a : Nat) : Nat :=
  (if left then (a <<< 2) ^^^ ((a <<< 1) ||| a)
   else a ^^^ ((a <<< 1) ||| (a <<< 2))) % 2^20

def front (left : Bool) : Nat → Nat
  | 0 => 1
  | t+1 => step left (front left t)

theorem bit_initial (j : Nat) : (1:Nat).testBit j = decide (j=0) := by
  have h := Nat.testBit_bool_toNat true j
  simpa using h

theorem right_bits : ∀ t j, j<20 → (front false t).testBit j = R j t
  | 0,j,hj => by
    rw [front,bit_initial]
    by_cases hz : j=0
    · subst hz; rfl
    · simp [R,cell,hz]
  | t+1,j,hj => by
    simp only [front,step,Bool.false_eq_true,ite_false,Nat.testBit_mod_two_pow,
      hj,decide_true,Bool.true_and,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft]
    rcases j with _ | _ | j
    · simp [right_bits t 0 (by omega),R_zero]
    · simp [right_bits t 0 (by omega),right_bits t 1 (by omega),R_zero,R_one_succ]
    · simp only [show 1≤j+2 by omega,show 2≤j+2 by omega,decide_true,Bool.true_and,
        show j+2-1=j+1 by omega,show j+2-2=j by omega]
      rw [right_bits t (j+2) hj,right_bits t (j+1) (by omega),right_bits t j (by omega)]
      exact (R_step j t).symm

theorem left_bits : ∀ t j, j<20 → (front true t).testBit j = D j t
  | 0,j,hj => by
    rw [front,bit_initial]
    by_cases hz : j=0
    · subst hz; rfl
    · simp [D,cell,hz]
  | t+1,j,hj => by
    simp only [front,step,ite_true,Nat.testBit_mod_two_pow,
      hj,decide_true,Bool.true_and,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft]
    rcases j with _ | _ | j
    · simp [left_bits t 0 (by omega),D_zero]
    · simp [left_bits t 0 (by omega),D_zero,D_one]
    · simp only [show 1≤j+2 by omega,show 2≤j+2 by omega,decide_true,Bool.true_and,
        show j+2-1=j+1 by omega,show j+2-2=j by omega]
      rw [left_bits t (j+2) hj,left_bits t (j+1) (by omega),left_bits t j (by omega)]
      exact (D_step j t).symm

theorem front_agree (left : Bool) (a b : Nat) (h : front left a = front left b) :
    ∀ n, front left (a+n) = front left (b+n)
  | 0 => h
  | n+1 => by
    rw [show a+(n+1)=(a+n)+1 by omega,show b+(n+1)=(b+n)+1 by omega,front,front,
      front_agree left a b h n]

set_option maxHeartbeats 0 in
theorem right_cycle : front false 256 = 1 := by decide

set_option maxHeartbeats 0 in
theorem left_cycle : front true 24 = front true 20 := by decide

theorem right_periodic (t : Nat) : front false (t+256) = front false t := by
  have h := front_agree false 256 0 right_cycle t
  simpa [Nat.add_comm] using h

theorem left_periodic (t : Nat) (ht : 20≤t) : front true (t+4) = front true t := by
  have h := front_agree true 24 20 left_cycle (t-20)
  simpa [show 24+(t-20)=t+4 by omega,show 20+(t-20)=t by omega] using h

theorem right_reduce (t : Nat) : front false t = front false (t%256) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases ht : t<256
    · rw [Nat.mod_eq_of_lt ht]
    · rw [show t=(t-256)+256 by omega,right_periodic,ih (t-256) (by omega)]
      congr 1
      omega

theorem left_reduce (t : Nat) (ht : 20≤t) : front true t = front true (20+t%4) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases hsmall : t<24
    · congr 1; omega
    · rw [show t=(t-4)+4 by omega,left_periodic (t-4) (by omega),ih (t-4) (by omega) (by omega)]
      congr 1
      omega

def diagnostic : Bool :=
  (List.range 256).all fun r => (List.range 19).any fun j =>
    decide ((front true (20+(r+j)%4)).testBit j ≠ (front false ((r+j)%256)).testBit j)

set_option maxHeartbeats 0 in
theorem diagnostic_ok : diagnostic = true := by decide

def smallDiagnostic : Bool :=
  (List.range 19).all fun k => (List.range 19).any fun j =>
    decide ((front true (k+1+j)).testBit j ≠ (front false (k+1+j)).testBit j)

set_option maxHeartbeats 0 in
theorem small_diagnostic_ok : smallDiagnostic = true := by decide

theorem small_witness (m : Nat) (hm : 0<m) (hsmall : m<20) :
    ∃ j, j<19 ∧ (front true (m+j)).testBit j ≠ (front false (m+j)).testBit j := by
  have h := List.all_eq_true.mp small_diagnostic_ok (m-1) (List.mem_range.mpr (by omega))
  obtain ⟨j,hj,he⟩ := List.any_eq_true.mp h
  refine ⟨j,List.mem_range.mp hj,?_⟩
  simpa [show m-1+1=m by omega] using he

theorem large_witness (m : Nat) (hm : 20≤m) :
    ∃ j, j<19 ∧ (front true (m+j)).testBit j ≠ (front false (m+j)).testBit j := by
  have h := List.all_eq_true.mp diagnostic_ok (m%256) (List.mem_range.mpr (by omega))
  obtain ⟨j,hj,he⟩ := List.any_eq_true.mp h
  refine ⟨j,List.mem_range.mp hj,?_⟩
  rw [left_reduce (m+j) (by omega),right_reduce]
  have h4 : (m+j)%4 = (m%256+j)%4 := by omega
  have h256 : (m+j)%256 = (m%256+j)%256 := by omega
  rw [h4,h256]
  exact of_decide_eq_true he

/-- An unbounded family: every pair of distinct mirror columns differs no
later than 18 steps after the first black cell reaches those columns. -/
theorem mirror_columns_distinguishable (m : Nat) (hm : 0<m) :
    ∃ j, j≤18 ∧ cell (m+j) (-(m:Int)) ≠ cell (m+j) (m:Int) := by
  obtain ⟨j,hj,he⟩ := if hs : m<20 then small_witness m hm hs else large_witness m (by omega)
  refine ⟨j,by omega,?_⟩
  rw [left_bits (m+j) j (by omega),right_bits (m+j) j (by omega)] at he
  simpa only [D,R,show (j:Int)-((m+j:Nat):Int)=-(m:Int) by omega,
    show ((m+j:Nat):Int)-(j:Int)=(m:Int) by omega] using he

theorem first_arrival_black (p : Int) : cell p.natAbs p = true := by
  generalize hm : p.natAbs = m
  rcases Int.natAbs_eq_iff.mp hm with hp | hp
  · rw [hp]; simpa [R] using R_zero m
  · rw [hp]; exact cell_left_edge m

theorem white_before_arrival (t : Nat) (p : Int) (ht : t<p.natAbs) : cell t p = false := by
  rcases Int.natAbs_eq_iff.mp (rfl : p.natAbs=p.natAbs) with hp | hp
  · rw [hp]; exact cell_eq_false_of_gt t _ (by omega)
  · rw [hp]; exact cell_eq_false_of_lt t _ (by omega)

/-- Every two different spatial columns of the single-seed pattern have
different complete traces, with an explicit observation-time bound. This
does not assert anything about eventual equality or temporal periodicity. -/
theorem columns_distinguishable (p q : Int) (hne : p≠q) :
    ∃ t, t≤max p.natAbs q.natAbs+18 ∧ cell t p ≠ cell t q := by
  rcases Nat.lt_trichotomy p.natAbs q.natAbs with hlt | heq | hgt
  · refine ⟨p.natAbs,by omega,?_⟩
    rw [first_arrival_black,white_before_arrival _ _ hlt]
    decide
  · have hop : p = -q := (Int.natAbs_eq_natAbs_iff.mp heq).resolve_left hne
    cases q with
    | ofNat m =>
      change p≠(m:Int) at hne
      change p.natAbs=m at heq
      change p=-(m:Int) at hop
      have hm : 0<m := by omega
      obtain ⟨j,hj,hw⟩ := mirror_columns_distinguishable m hm
      refine ⟨m+j,by omega,?_⟩
      simpa only [hop,Int.ofNat_eq_natCast] using hw
    | negSucc m =>
      obtain ⟨j,hj,hw⟩ := mirror_columns_distinguishable (m+1) (by omega)
      refine ⟨m+1+j,by omega,?_⟩
      simpa [hop,Int.negSucc_eq] using Ne.symm hw
  · refine ⟨q.natAbs,by omega,?_⟩
    rw [first_arrival_black,white_before_arrival _ _ hgt]
    decide

theorem columns_injective {p q : Int} (h : ∀ t, cell t p = cell t q) : p=q := by
  by_cases heq : p=q
  · exact heq
  · obtain ⟨t,_,ht⟩ := columns_distinguishable p q heq
    exact False.elim (ht (h t))

end Rule30Submission
", "ProjectDir" -> $Rule30PrizeKit];
rule30KernelCheck = rule30Submission["Rule30Submission.columns_distinguishable"]["KernelCheck"]

Out[4]=
Success["KernelChecked", Association["MessageTemplate" ->
   "The kernel accepts all `1` declarations of `2`.", "MessageParameters" ->
   {85, "LeanLinkTmp33396127677076639817x68228"},
  "Module" -> "LeanLinkTmp33396127677076639817x68228", "Declarations" -> 85]]

In[5]:=  rule30Submission["Rule30Submission.columns_distinguishable"]["TypeForm"]

Out[5]=
"∀ (p q : ℤ),
  p ≠ q →
    ∃ t ≤ max p.natAbs q.natAbs + 18,
      Ruliology.CellularAutomata.Rule30Jen.cell t p ≠ Ruliology.CellularAutomata.Rule30Jen.cell t q"

In[6]:=
AssociationMap[rule30Submission[#]["Axioms"] &,
 {"Rule30Submission.columns_distinguishable", "Rule30Submission.mirror_columns_distinguishable",
  "Rule30Submission.columns_injective"}]

Out[6]=  <|"Rule30Submission.columns_distinguishable" -> {"Classical.choice", "Quot.sound", "propext"}, "Rule30Submission.mirror_columns_distinguishable" -> {"Classical.choice", "Quot.sound", "propext"}, "Rule30Submission.columns_injective" -> {"Classical.choice", "Quot.sound", "propext"}|>
```

## Scope and reproducibility

The core Lean catalog proof and its exact checker reports are in [PR 6](https://github.com/WolframInstitute/Rule30PrizeKit/pull/6). The source was checked against both the current catalog and the pinned reference kit. Building and evaluating this notebook is separate from submitting it to the prize API. This build script never submits anything.

The earlier trace-reconstruction work and its open hypothesis remain distinct: separating every spatial column of the one-seed pattern does not establish edge recovery for arbitrary finite initial rows. Problem 1 remains open.
