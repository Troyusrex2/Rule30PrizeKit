---
Template: ComputationalEssay
Name: Distinguishing every pair of Rule 30 spatial columns
Author: Troy Lowry; OpenAI Codex
Date: 2026-10-23
Description: An unbounded spatial theorem from kernel-checked edge cycles
Abstract: Every two distinct spatial columns p and q of the single-seed Rule 30 pattern differ by time max(abs(p),abs(q))+18. The mirror case is proved with 20-bit edge windows, certified periods and all 256 phase classes. This is injectivity of complete traces starting at time zero. It does not prove temporal nonperiodicity, exclude eventual equality, or solve a prize problem.
Keywords: [Rule 30, spatial columns, finite certificates, Lean]
---

## The statement

For every pair of integers p != q there is a natural time t with

    t <= max(abs(p), abs(q)) + 18

at which the cells in columns p and q differ. This covers arbitrarily large
positions. The statement concerns complete traces beginning at time zero.
It does not exclude eventual equality of two columns and does not answer
whether the center column becomes periodic. No literature-first claim is made.

```wl
ArrayPlot[CellularAutomaton[30,{{1},0},{64,{-64,64}}], Frame->True,
  PlotLabel->"Rule 30 from one black cell"]
```

## Why a finite check proves an unbounded family

A column at position p is white before time abs(p), then black at that time.
Thus different distances from the seed have different traces. The remaining
case consists of the mirror columns -m and m.

Track the first 20 cells behind each moving edge. The right window returns
to its initial state after 256 steps. The left window enters a four-step cycle
after time 20. These are exact finite-state equalities, checked by Lean's
ordinary kernel. Induction extends the cycles to all future times. The 256
possible phases each have a witness among offsets 0 through 18. Small initial
exceptions are checked separately. The window bits are proved equal to the
official cellwise diagonals, so this proves the mirror result for every m>0.

## Independent Wolfram computation

The following built-in cellular automaton computation independently checks the
finite cycles, all 256 phases and 512 sample mirror pairs. These samples are
not the justification for the all-position quantifier; the Lean proof below is.

```wl
ClearAll[columnFrontReport];
columnFrontReport[] := Module[{grid,left,right,lags,residues},
  grid=CellularAutomaton[30,{{1},0},{530,{-530,530}}];
  left[t_]:=Sum[grid[[t+1,531-t+j]] 2^j,{j,0,19}];
  right[t_]:=Sum[grid[[t+1,531+t-j]] 2^j,{j,0,19}];
  lags=Table[FirstPosition[Table[
    Unequal[grid[[m+j+1,531-m]],grid[[m+j+1,531+m]]],{j,0,18}],True,
    Missing["NoWitness"]],{m,1,512}];
  residues=Table[AnyTrue[Range[0,18],Function[j,
    BitGet[left[20+Mod[r+j,4]],j]!=BitGet[right[Mod[r+j,256]],j]]],{r,0,255}];
  <|"engineVersion"->$VersionNumber,"finiteCrosschecksOnly"->True,
    "gridDimensions"->Dimensions[grid],"frontWidth"->20,
    "rightCycleCloses"->SameQ[right[256],right[0]],
    "leftCycleCloses"->SameQ[left[24],left[20]],
    "leftCycle"->Table[left[t],{t,20,23}],
    "all256ResiduesSeparated"->And@@residues,
    "all512SampleMirrorPairsSeparated"->FreeQ[lags,_Missing],
    "exampleM256Lag"->First[lags[[256]]]-1|>
];

columnFrontReport[]
```

## The complete formal proof

This self-contained source carries the proof; it does not rely on an unmerged
research module being installed in the reference kit. The proof bodies match
the catalog contribution, with namespace and module wrappers adapted. The
underlying catalog diagonal theorems are imported unchanged.

```wl
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit = Environment["RULE30PRIZE_KIT"];
```

```wl
rule30Submission = LeanImportString["import Rule30PrizeKit\n\nimport Ruliology.CellularAutomata.Rule30Diagonals\nimport Ruliology.CellularAutomata.Rule30Prize\n\n/-!\n# Pairwise distinct complete column traces of the single-seed pattern\n\nFor every pair of integers p != q, an observation at time at most\nmax(|p|,|q|)+18 distinguishes their columns. First arrival distinguishes\ndifferent distances from the seed. Mirror columns -m and m differ by time\nm+18, using certified 20-bit edge windows: the left window is 4-periodic\nafter time 20 and the right window is 256-periodic from the start. Checking\nall 256 phase classes gives the uniform bound for arbitrarily large m.\n\nThis concerns complete traces starting at time zero. It does not exclude\neventual equality, prove temporal nonperiodicity, or solve a prize problem.\n-/\n\n\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nopen Ruliology.CellularAutomata\n\nnamespace Rule30Submission\n\nopen Rule30Jen Rule30Diagonals\n\ndef step (left : Bool) (a : Nat) : Nat :=\n  (if left then (a <<< 2) ^^^ ((a <<< 1) ||| a)\n   else a ^^^ ((a <<< 1) ||| (a <<< 2))) % 2^20\n\ndef front (left : Bool) : Nat → Nat\n  | 0 => 1\n  | t+1 => step left (front left t)\n\ntheorem bit_initial (j : Nat) : (1:Nat).testBit j = decide (j=0) := by\n  have h := Nat.testBit_bool_toNat true j\n  simpa using h\n\ntheorem right_bits : ∀ t j, j<20 → (front false t).testBit j = R j t\n  | 0,j,hj => by\n    rw [front,bit_initial]\n    by_cases hz : j=0\n    · subst hz; rfl\n    · simp [R,cell,hz]\n  | t+1,j,hj => by\n    simp only [front,step,Bool.false_eq_true,ite_false,Nat.testBit_mod_two_pow,\n      hj,decide_true,Bool.true_and,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft]\n    rcases j with _ | _ | j\n    · simp [right_bits t 0 (by omega),R_zero]\n    · simp [right_bits t 0 (by omega),right_bits t 1 (by omega),R_zero,R_one_succ]\n    · simp only [show 1≤j+2 by omega,show 2≤j+2 by omega,decide_true,Bool.true_and,\n        show j+2-1=j+1 by omega,show j+2-2=j by omega]\n      rw [right_bits t (j+2) hj,right_bits t (j+1) (by omega),right_bits t j (by omega)]\n      exact (R_step j t).symm\n\ntheorem left_bits : ∀ t j, j<20 → (front true t).testBit j = D j t\n  | 0,j,hj => by\n    rw [front,bit_initial]\n    by_cases hz : j=0\n    · subst hz; rfl\n    · simp [D,cell,hz]\n  | t+1,j,hj => by\n    simp only [front,step,ite_true,Nat.testBit_mod_two_pow,\n      hj,decide_true,Bool.true_and,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft]\n    rcases j with _ | _ | j\n    · simp [left_bits t 0 (by omega),D_zero]\n    · simp [left_bits t 0 (by omega),D_zero,D_one]\n    · simp only [show 1≤j+2 by omega,show 2≤j+2 by omega,decide_true,Bool.true_and,\n        show j+2-1=j+1 by omega,show j+2-2=j by omega]\n      rw [left_bits t (j+2) hj,left_bits t (j+1) (by omega),left_bits t j (by omega)]\n      exact (D_step j t).symm\n\ntheorem front_agree (left : Bool) (a b : Nat) (h : front left a = front left b) :\n    ∀ n, front left (a+n) = front left (b+n)\n  | 0 => h\n  | n+1 => by\n    rw [show a+(n+1)=(a+n)+1 by omega,show b+(n+1)=(b+n)+1 by omega,front,front,\n      front_agree left a b h n]\n\nset_option maxHeartbeats 0 in\ntheorem right_cycle : front false 256 = 1 := by decide\n\nset_option maxHeartbeats 0 in\ntheorem left_cycle : front true 24 = front true 20 := by decide\n\ntheorem right_periodic (t : Nat) : front false (t+256) = front false t := by\n  have h := front_agree false 256 0 right_cycle t\n  simpa [Nat.add_comm] using h\n\ntheorem left_periodic (t : Nat) (ht : 20≤t) : front true (t+4) = front true t := by\n  have h := front_agree true 24 20 left_cycle (t-20)\n  simpa [show 24+(t-20)=t+4 by omega,show 20+(t-20)=t by omega] using h\n\ntheorem right_reduce (t : Nat) : front false t = front false (t%256) := by\n  induction t using Nat.strongRecOn with\n  | ind t ih =>\n    by_cases ht : t<256\n    · rw [Nat.mod_eq_of_lt ht]\n    · rw [show t=(t-256)+256 by omega,right_periodic,ih (t-256) (by omega)]\n      congr 1\n      omega\n\ntheorem left_reduce (t : Nat) (ht : 20≤t) : front true t = front true (20+t%4) := by\n  induction t using Nat.strongRecOn with\n  | ind t ih =>\n    by_cases hsmall : t<24\n    · congr 1; omega\n    · rw [show t=(t-4)+4 by omega,left_periodic (t-4) (by omega),ih (t-4) (by omega) (by omega)]\n      congr 1\n      omega\n\ndef diagnostic : Bool :=\n  (List.range 256).all fun r => (List.range 19).any fun j =>\n    decide ((front true (20+(r+j)%4)).testBit j ≠ (front false ((r+j)%256)).testBit j)\n\nset_option maxHeartbeats 0 in\ntheorem diagnostic_ok : diagnostic = true := by decide\n\ndef smallDiagnostic : Bool :=\n  (List.range 19).all fun k => (List.range 19).any fun j =>\n    decide ((front true (k+1+j)).testBit j ≠ (front false (k+1+j)).testBit j)\n\nset_option maxHeartbeats 0 in\ntheorem small_diagnostic_ok : smallDiagnostic = true := by decide\n\ntheorem small_witness (m : Nat) (hm : 0<m) (hsmall : m<20) :\n    ∃ j, j<19 ∧ (front true (m+j)).testBit j ≠ (front false (m+j)).testBit j := by\n  have h := List.all_eq_true.mp small_diagnostic_ok (m-1) (List.mem_range.mpr (by omega))\n  obtain ⟨j,hj,he⟩ := List.any_eq_true.mp h\n  refine ⟨j,List.mem_range.mp hj,?_⟩\n  simpa [show m-1+1=m by omega] using he\n\ntheorem large_witness (m : Nat) (hm : 20≤m) :\n    ∃ j, j<19 ∧ (front true (m+j)).testBit j ≠ (front false (m+j)).testBit j := by\n  have h := List.all_eq_true.mp diagnostic_ok (m%256) (List.mem_range.mpr (by omega))\n  obtain ⟨j,hj,he⟩ := List.any_eq_true.mp h\n  refine ⟨j,List.mem_range.mp hj,?_⟩\n  rw [left_reduce (m+j) (by omega),right_reduce]\n  have h4 : (m+j)%4 = (m%256+j)%4 := by omega\n  have h256 : (m+j)%256 = (m%256+j)%256 := by omega\n  rw [h4,h256]\n  exact of_decide_eq_true he\n\n/-- An unbounded family: every pair of distinct mirror columns differs no\nlater than 18 steps after the first black cell reaches those columns. -/\ntheorem mirror_columns_distinguishable (m : Nat) (hm : 0<m) :\n    ∃ j, j≤18 ∧ cell (m+j) (-(m:Int)) ≠ cell (m+j) (m:Int) := by\n  obtain ⟨j,hj,he⟩ := if hs : m<20 then small_witness m hm hs else large_witness m (by omega)\n  refine ⟨j,by omega,?_⟩\n  rw [left_bits (m+j) j (by omega),right_bits (m+j) j (by omega)] at he\n  simpa only [D,R,show (j:Int)-((m+j:Nat):Int)=-(m:Int) by omega,\n    show ((m+j:Nat):Int)-(j:Int)=(m:Int) by omega] using he\n\ntheorem first_arrival_black (p : Int) : cell p.natAbs p = true := by\n  generalize hm : p.natAbs = m\n  rcases Int.natAbs_eq_iff.mp hm with hp | hp\n  · rw [hp]; simpa [R] using R_zero m\n  · rw [hp]; exact cell_left_edge m\n\ntheorem white_before_arrival (t : Nat) (p : Int) (ht : t<p.natAbs) : cell t p = false := by\n  rcases Int.natAbs_eq_iff.mp (rfl : p.natAbs=p.natAbs) with hp | hp\n  · rw [hp]; exact cell_eq_false_of_gt t _ (by omega)\n  · rw [hp]; exact cell_eq_false_of_lt t _ (by omega)\n\n/-- Every two different spatial columns of the single-seed pattern have\ndifferent complete traces, with an explicit observation-time bound. This\ndoes not assert anything about eventual equality or temporal periodicity. -/\ntheorem columns_distinguishable (p q : Int) (hne : p≠q) :\n    ∃ t, t≤max p.natAbs q.natAbs+18 ∧ cell t p ≠ cell t q := by\n  rcases Nat.lt_trichotomy p.natAbs q.natAbs with hlt | heq | hgt\n  · refine ⟨p.natAbs,by omega,?_⟩\n    rw [first_arrival_black,white_before_arrival _ _ hlt]\n    decide\n  · have hop : p = -q := (Int.natAbs_eq_natAbs_iff.mp heq).resolve_left hne\n    cases q with\n    | ofNat m =>\n      change p≠(m:Int) at hne\n      change p.natAbs=m at heq\n      change p=-(m:Int) at hop\n      have hm : 0<m := by omega\n      obtain ⟨j,hj,hw⟩ := mirror_columns_distinguishable m hm\n      refine ⟨m+j,by omega,?_⟩\n      simpa only [hop,Int.ofNat_eq_natCast] using hw\n    | negSucc m =>\n      obtain ⟨j,hj,hw⟩ := mirror_columns_distinguishable (m+1) (by omega)\n      refine ⟨m+1+j,by omega,?_⟩\n      simpa [hop,Int.negSucc_eq] using Ne.symm hw\n  · refine ⟨q.natAbs,by omega,?_⟩\n    rw [first_arrival_black,white_before_arrival _ _ hgt]\n    decide\n\ntheorem columns_injective {p q : Int} (h : ∀ t, cell t p = cell t q) : p=q := by\n  by_cases heq : p=q\n  · exact heq\n  · obtain ⟨t,_,ht⟩ := columns_distinguishable p q heq\n    exact False.elim (ht (h t))\n\nend Rule30Submission\n", "ProjectDir" -> $Rule30PrizeKit];
rule30KernelCheck = rule30Submission["Rule30Submission.columns_distinguishable"]["KernelCheck"]
```

```wl
rule30Submission["Rule30Submission.columns_distinguishable"]["TypeForm"]
```

```wl
AssociationMap[rule30Submission[#]["Axioms"] &,
 {"Rule30Submission.columns_distinguishable", "Rule30Submission.mirror_columns_distinguishable",
  "Rule30Submission.columns_injective"}]
```

## Scope and reproducibility

The core Lean catalog proof and its exact checker reports are in
[PR 6](https://github.com/WolframInstitute/Rule30PrizeKit/pull/6).
The source was checked against both the current catalog and the pinned
reference kit. Building and evaluating this notebook is separate from
submitting it to the prize API. This build script never submits anything.

The earlier trace-reconstruction work and its open hypothesis remain distinct:
separating every spatial column of the one-seed pattern does not establish
edge recovery for arbitrary finite initial rows. Problem 1 remains open.
