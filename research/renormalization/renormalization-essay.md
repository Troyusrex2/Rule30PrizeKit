---
Template: ComputationalEssay
Name: An eight-column reconstruction identity and the limits of its iteration
Author: Troy Lowry; OpenAI Codex
Date: 2026-10-24
Description: A core Lean identity, exact preservation criterion and checked counterexamples
Abstract: For a spaced boundary gate, Rule 30 sideways reconstruction translates eight columns by a simple gate transform. The spacing survives exactly when the original gate is white from index four onward. A period-five gate disproves unconditional iteration, and a period-31 spacing-three/five gate produces seventeen consecutive white initial cells. No prize problem or eventual period two is excluded.
Keywords: [Rule 30, reconstruction, renormalization, Lean, counterexamples]
---

## Scope and source

This essay is prepared for human review and has not been submitted to the prize
API. It proves a partial structural identity and identifies two gaps in stronger
extrapolations. It does not exclude eventual period two or solve a prize problem.
No finite driven-right realization of the example gates is asserted.

The one-step identity follows the informal identity in
[morpholib Theorem 14](https://github.com/fractastical/morpholib/blob/777865115483d310f72f0b9511b45409e330a8f5/docs/RULE30_PRIZE_SUBMISSION.md).
That source is credited for the identity. The Lean formalization, support
transfer, exact preservation criterion, packed-cone soundness theorem and
counterexamples here were developed by Troy Lowry with OpenAI Codex. No claim
of literature priority is made. The source's advertised global period-two
elimination is not used as a premise.

## The identity and its required condition

Let b_G(2r)=!G(r), b_G(2r+1)=1 and D G(r)=G(r+2) xor G(r+4).
Call G spaced when black cells never have distance one or two.
For every spaced G, every m >= 1 and every time t, the kit's scalar
reconstruction satisfies

    recon b_G (m+8) t = recon b_(D G) m t.

An initial support bound W transfers to W-8. The preservation criterion is
exact: D G is spaced if and only if G(r+4)=0 for every r. Thus this particular
spacing hypothesis cannot be carried through a second step for an infinite
gate. Other renormalizations remain possible.

## Independent finite observations

The following scalar reconstruction compares 12,800 cells. It also checks a
period-five counterexample to applying the translation twice, and seventeen
white initial cells at depths 528 through 544 for a period-31 gate whose black
spacings are only three or five. These observations are independently connected
to the kit's scalar reconstruction by Lean below.

```wl
(* Independent scalar reconstruction, finite observations only. *)
ClearAll[spacingColumns, spacingReport];
spacingColumns[gate_, depth_Integer, horizon_Integer] := Module[
  {old, current, next, result, count = horizon + depth},
  old = ConstantArray[False, count];
  current = Table[If[EvenQ[t], Not[gate[Quotient[t, 2]]], True], {t, 0, count - 1}];
  result = {old, current};
  Do[
    next = Table[Xor[current[[t + 2]], Or[current[[t + 1]], old[[t + 1]]]],
      {t, 0, Length[current] - 2}];
    old = current; current = next; AppendTo[result, current],
    {k, 2, depth}];
  result
];
spacingReport[] := Module[{cases, checks, g5, dg5, ddg5, c, c2, mismatch},
  (* Periodic gates with minimum spacing three; no use of simulated Rule30 output. *)
  cases = {Function[r, False], Function[r, Mod[r, 3] == 0],
    Function[r, Mod[r, 5] == 0], Function[r, MemberQ[{0, 3}, Mod[r, 8]]],
    Function[r, MemberQ[{0, 5, 8}, Mod[r, 13]]]};
  checks = Table[Module[{g = gate, dg, a, b},
    dg = Function[r, Xor[g[r + 2], g[r + 4]]];
    a = spacingColumns[g, 48, 64]; b = spacingColumns[dg, 40, 64];
    And @@ Flatten[Table[a[[m + 9, t + 1]] == b[[m + 1, t + 1]],
      {m, 1, 40}, {t, 0, 63}]]], {gate, cases}];
  g5 = Function[r, Mod[r, 5] == 0];
  dg5 = Function[r, Xor[g5[r + 2], g5[r + 4]]];
  ddg5 = Function[r, Xor[dg5[r + 2], dg5[r + 4]]];
  c = spacingColumns[g5, 17, 1]; c2 = spacingColumns[ddg5, 1, 1];
  mismatch = {c[[18, 1]], c2[[2, 1]]};
  <|"FiniteExperimentsOnly" -> True, "TranslationChecks" -> checks,
    "CellsCompared" -> Length[cases]*40*64,
    "PeriodFiveInitialSpacing" -> And @@ Table[
      Not[g5[r] && g5[r + 1]] && Not[g5[r] && g5[r + 2]], {r, 0, 9}],
    "TransformedGateAtIndices1And3" -> {dg5[1], dg5[3]},
    "SecondTranslationDepth17Time0" -> mismatch,
    "SecondTranslationFails" -> Unequal @@ mismatch,
    "FullProblemClaim" -> False|>
];

ClearAll[spacingGapReport];
spacingGapReport[] := Module[{g, columns, whites},
  g = Function[r, MemberQ[{0,3,6,9,12,15,18,21,26}, Mod[r,31]]];
  columns = spacingColumns[g, 544, 1];
  whites = Table[columns[[d+1,1]], {d,528,544}];
  <|"FiniteExperimentOnly" -> True, "GatePeriod" -> 31,
    "WhiteDepths" -> Range[528,544], "ObservedCells" -> whites,
    "AllSeventeenWhite" -> And @@ (Not /@ whites),
    "GapConstraintCheckedAcrossTwoPeriods" -> And @@ Table[
      If[g[r], (!g[r+1] && !g[r+2] &&
        (g[r+3] || (!g[r+3] && !g[r+4] && g[r+5]))), True], {r,0,61}],
    "FiniteRightRealizabilityClaim" -> False, "FullProblemClaim" -> False|>
];

{spacingReport[], spacingGapReport[]}
```

The period-five example gives white at depth 17, time 0, where the twice
transformed formula gives black. The period-31 example rules out a universal
maximum white gap of sixteen under the spacing-three/five restriction alone.
It does not rule out every larger gap bound.

## Exact embedded Lean source and full kernel replay

The code imports only the kit's core reconstruction and official statement
modules. The packed-cone soundness theorem states its finite light-cone bound.
The proof contains no new axioms, native decision procedure or custom elaborator.

```wl
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit = Environment["RULE30PRIZE_KIT"];
```

```wl
rule30Submission = LeanImportString["import Ruliology.CellularAutomata.Rule30ZeroBoundary\nimport Ruliology.CellularAutomata.Rule30Prize\n\nopen Ruliology.CellularAutomata\n\n/-!\n# An eight-column reconstruction identity and the condition needed to iterate it\n\nThe boundary history is `!G 0, 1, !G 1, 1, ...`. If the black gate\npositions have spacing at least three, shifting reconstruction eight columns\nleft replaces `G r` by `G (r+2) xor G (r+4)`. This condition is not asserted\nto hold after that replacement, or for every driven right half.\n-/\n\n\n\nnamespace Rule30Submission.Spacing\n\nopen Rule30ZeroBoundary\n\ndef boundary (G : Nat → Bool) (t : Nat) : Bool :=\n  if t % 2 = 0 then !G (t / 2) else true\n\ndef transform (G : Nat → Bool) (r : Nat) : Bool := xor (G (r+2)) (G (r+4))\n\ndef Spaced (G : Nat → Bool) : Prop :=\n  ∀ r, (G r && G (r+1)) = false ∧ (G r && G (r+2)) = false\n\n/-- The even/odd pair of a reconstructed column. -/\ndef pair (G : Nat → Bool) : Nat → Nat → Bool × Bool\n  | 0, _ => (false, false)\n  | 1, r => (!G r, true)\n  | k+2, r =>\n      (xor (pair G (k+1) r).2 ((pair G (k+1) r).1 || (pair G k r).1),\n       xor (pair G (k+1) (r+1)).1 ((pair G (k+1) r).2 || (pair G k r).2))\n\ntheorem boundary_even (G : Nat → Bool) (r : Nat) : boundary G (2*r) = !G r := by\n  simp [boundary, show 2*r % 2 = 0 by omega,\n    show 2*r / 2 = r by omega]\n\ntheorem boundary_odd (G : Nat → Bool) (r : Nat) : boundary G (2*r+1) = true := by\n  simp [boundary]\n\n/-- The pair recurrence is exactly the kit's scalar reconstruction. -/\ntheorem pair_recon (G : Nat → Bool) : ∀ k r,\n    pair G k r = (recon (boundary G) k (2*r), recon (boundary G) k (2*r+1))\n  | 0, r => rfl\n  | 1, r => by simp [pair, recon, boundary_even, boundary_odd]\n  | k+2, r => by\n      rw [pair, pair_recon G (k+1) r, pair_recon G (k+1) (r+1), pair_recon G k r]\n      simp only [recon_two, show 2*r+1+1 = 2*(r+1) by omega]\n\nset_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\ntheorem ninth_pair (G : Nat → Bool) (h : Spaced G) (r : Nat) :\n    pair G 9 r = pair (transform G) 1 r := by\n  have h0 := h r\n  have h1 := h (r+1)\n  have h2 := h (r+2)\n  have h3 := h (r+3)\n  simp only [Nat.add_assoc] at h1 h2 h3\n  simp only [pair, transform, Nat.add_assoc]\n  cases ha : G r <;> cases hb : G (r+1) <;> cases hc : G (r+2) <;>\n    cases hd : G (r+3) <;> cases he : G (r+4) <;> simp_all\n\nset_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\ntheorem tenth_pair (G : Nat → Bool) (h : Spaced G) (r : Nat) :\n    pair G 10 r = pair (transform G) 2 r := by\n  have h0 := h r\n  have h1 := h (r+1)\n  have h2 := h (r+2)\n  have h3 := h (r+3)\n  have h4 := h (r+4)\n  simp only [Nat.add_assoc] at h1 h2 h3 h4\n  simp only [pair, transform, Nat.add_assoc]\n  cases ha : G r <;> cases hb : G (r+1) <;> cases hc : G (r+2) <;>\n    cases hd : G (r+3) <;> cases he : G (r+4) <;> cases hf : G (r+5) <;> simp_all\n\n/-- An exact eight-column translation, with an explicit spacing premise. -/\ntheorem pair_translate (G : Nat → Bool) (h : Spaced G) : ∀ m r,\n    pair G (m+9) r = pair (transform G) (m+1) r := by\n  have key : ∀ m, (∀ r, pair G (m+9) r = pair (transform G) (m+1) r) ∧\n      (∀ r, pair G (m+10) r = pair (transform G) (m+2) r) := by\n    intro m\n    induction m with\n    | zero => exact ⟨ninth_pair G h, tenth_pair G h⟩\n    | succ m ih =>\n        refine ⟨ih.2, fun r => ?_⟩\n        change\n          (xor (pair G (m+10) r).2 ((pair G (m+10) r).1 || (pair G (m+9) r).1),\n           xor (pair G (m+10) (r+1)).1 ((pair G (m+10) r).2 || (pair G (m+9) r).2)) =\n          (xor (pair (transform G) (m+2) r).2\n             ((pair (transform G) (m+2) r).1 || (pair (transform G) (m+1) r).1),\n           xor (pair (transform G) (m+2) (r+1)).1\n             ((pair (transform G) (m+2) r).2 || (pair (transform G) (m+1) r).2))\n        rw [ih.2 r, ih.2 (r+1), ih.1 r]\n  exact fun m => (key m).1\n\n/-- The scalar statement holds at every time, not only at time zero. -/\ntheorem reconstruction_translate (G : Nat → Bool) (h : Spaced G) (m t : Nat) :\n    recon (boundary G) (m+9) t = recon (boundary (transform G)) (m+1) t := by\n  have hp := pair_translate G h m (t/2)\n  rw [pair_recon, pair_recon] at hp\n  rcases Nat.mod_two_eq_zero_or_one t with ht | ht\n  · have he : t = 2*(t/2) := by omega\n    rw [he]\n    exact congrArg Prod.fst hp\n  · have he : t = 2*(t/2)+1 := by omega\n    rw [he]\n    exact congrArg Prod.snd hp\n\n/-- An explicit support bound drops by eight under the translation. -/\ntheorem support_transfer (G : Nat → Bool) (h : Spaced G) (W : Nat)\n    (hW : ∀ k, W < k → lam (boundary G) k = false) :\n    ∀ k, W-8 < k → lam (boundary (transform G)) k = false := by\n  intro k hk\n  obtain ⟨m, rfl⟩ : ∃ m, k = m+1 := ⟨k-1, by omega⟩\n  unfold lam\n  rw [← reconstruction_translate G h]\n  exact hW _ (by omega)\n\n/-- A finite reconstructed initial row remains finite after the translation. -/\ntheorem finite_transfer (G : Nat → Bool) (h : Spaced G)\n    (hf : FinSupp (lam (boundary G))) : FinSupp (lam (boundary (transform G))) := by\n  obtain ⟨W, hW⟩ := hf\n  exact ⟨W-8, support_transfer G h W hW⟩\n\n/-- The spacing premise survives one transform exactly for gates white beyond\nindex three. Thus an infinite gate cannot support a second application. -/\ntheorem transform_spaced_iff (G : Nat → Bool) (h : Spaced G) :\n    Spaced (transform G) ↔ ∀ r, G (r+4) = false := by\n  constructor\n  · intro ht r\n    have ha := (h (r+2)).2\n    have hb := (h (r+4)).2\n    have hc := (ht r).2\n    simp only [transform, Nat.add_assoc] at hc ha hb\n    cases h2 : G (r+2) <;> cases h4 : G (r+4) <;> cases h6 : G (r+6) <;> simp_all\n  · intro hz\n    have he : transform G = fun r => G (r+2) := by\n      funext r\n      simp [transform, hz r]\n    rw [he]\n    intro r\n    simpa only [Nat.add_assoc] using h (r+2)\n\n/-- Spacing is not preserved: a period-five gate supplies a counterexample. -/\ndef periodFive (r : Nat) : Bool := r % 5 == 0\n\ntheorem periodFive_spaced : Spaced periodFive := by\n  intro r\n  have hr := Nat.mod_lt r (by decide : 0 < 5)\n  have h1 : (r+1)%5 = (r%5+1)%5 := by omega\n  have h2 : (r+2)%5 = (r%5+2)%5 := by omega\n  simp only [periodFive]\n  rw [h1, h2]\n  have hs : r%5=0 ∨ r%5=1 ∨ r%5=2 ∨ r%5=3 ∨ r%5=4 := by omega\n  rcases hs with hh | hh | hh | hh | hh <;> rw [hh] <;> decide\n\ntheorem transform_not_spaced : ¬ Spaced (transform periodFive) := by\n  intro h\n  have hh := (h 1).2\n  change true = false at hh\n  exact Bool.noConfusion hh\n\nset_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\n/-- Dropping the spacing premise for the second step gives a false identity,\nalready at depth seventeen and time zero for the period-five gate. -/\ntheorem second_translation_fails :\n    recon (boundary periodFive) 17 0 ≠\n      recon (boundary (transform (transform periodFive))) 1 0 := by\n  decide\n\nend Rule30Submission.Spacing\n\n/-!\n# Finite packed checks of the scalar sideways reconstruction\n\nEach natural number holds a column's successive times in its bits. A right\nshift reads the next time, so the packed update is the scalar inverse rule.\nThe soundness bound explicitly excludes the unrepresented future boundary.\n-/\n\n\n\nnamespace Rule30Submission.Packed\n\nopen Rule30ZeroBoundary Rule30Submission.Spacing\n\nnoncomputable def advance : Nat → Nat → Nat → Nat × Nat :=\n  Nat.rec (motive := fun _ => Nat → Nat → Nat × Nat)\n    (fun a b => (a,b))\n    (fun _ ih a b => ih b (Nat.xor (Nat.shiftRight b 1) (Nat.lor b a)))\n\ntheorem advance_zero (a b : Nat) : advance 0 a b = (a,b) := rfl\n\ntheorem advance_succ (k a b : Nat) :\n    advance (k+1) a b = advance k b ((b >>> 1) ^^^ (b ||| a)) := rfl\n\ntheorem advance_last : ∀ k a b,\n    advance (k+1) a b =\n      ((advance k a b).2,\n       ((advance k a b).2 >>> 1) ^^^ ((advance k a b).2 ||| (advance k a b).1))\n  | 0,a,b => rfl\n  | k+1,a,b => by\n      rw [advance_succ, advance_succ k a b, advance_last]\n\nnoncomputable def packedRun (B k : Nat) : Nat × Nat := advance k 0 B\n\ntheorem packedRun_zero (B : Nat) : packedRun B 0 = (0,B) := rfl\n\ntheorem packedRun_succ (B k : Nat) :\n    packedRun B (k+1) =\n      ((packedRun B k).2,\n       ((packedRun B k).2 >>> 1) ^^^ ((packedRun B k).2 ||| (packedRun B k).1)) :=\n  advance_last k 0 B\n\n/-- Every checked bit agrees with scalar reconstruction inside its finite cone. -/\ntheorem packed_sound (B H : Nat) (b : Nat → Bool)\n    (hb : ∀ t, t < H → B.testBit t = b t) : ∀ k t, t+k < H →\n    (packedRun B k).1.testBit t = recon b k t ∧\n    (packedRun B k).2.testBit t = recon b (k+1) t := by\n  intro k\n  induction k with\n  | zero =>\n      intro t ht\n      exact ⟨by simp [packedRun_zero, recon], hb t ht⟩\n  | succ k ih =>\n      intro t ht\n      have h0 := ih t (by omega)\n      have h1 := ih (t+1) (by omega)\n      rw [packedRun_succ]\n      refine ⟨h0.2, ?_⟩\n      simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight]\n      rw [show 1+t=t+1 by omega, h1.2, h0.2, h0.1]\n      exact (recon_two b k t).symm\n\nend Rule30Submission.Packed\n\n/-!\n# A spacing-three/five gate with seventeen white initial cells\n\nThe gate is globally periodic of period 31, with gaps 3,3,3,3,3,3,3,5,5.\nIts reconstructed initial row is white at depths 528 through 544. A finite\npacked cone is proved equal to the kit's scalar reconstruction. There is no\nclaim that this gate is realized by a finite driven right half.\n-/\n\n\n\nnamespace Rule30Submission.Gap\n\nopen Rule30ZeroBoundary Rule30Submission.Spacing\nopen Rule30Submission.Packed\n\ndef gate31 (r : Nat) : Bool := decide (r%31 ∈ [0,3,6,9,12,15,18,21,26])\n\ndef Next35 (G : Nat → Bool) (r : Nat) : Prop :=\n  G (r+1) = false ∧ G (r+2) = false ∧\n    (G (r+3) = true ∨ (G (r+3) = false ∧ G (r+4) = false ∧ G (r+5) = true))\n\ntheorem gate31_periodic (r : Nat) : gate31 (r+31) = gate31 r := by\n  simp [gate31]\n\ntheorem gate31_residues : ∀ r : Fin 31, gate31 r = true → Next35 gate31 r := by\n  unfold Next35\n  decide\n\n/-- Every black gate cell is followed by a gap of exactly three or five. -/\ntheorem gate31_gaps (r : Nat) (hr : gate31 r = true) : Next35 gate31 r := by\n  have h := gate31_residues ⟨r%31, Nat.mod_lt r (by decide)⟩\n  simp only [Next35, gate31, Nat.add_mod, Nat.mod_mod] at h hr ⊢\n  exact h hr\n\ntheorem gate31_spaced : Spaced gate31 := by\n  intro r\n  cases hr : gate31 r with\n  | false => simp\n  | true =>\n      have h := gate31_gaps r hr\n      simp only [Next35] at h\n      simp [h.1, h.2.1]\n\n-- The finite boundary prefix is generated and cross-checked by the companion\n-- Python experiment. Its bits are rechecked below by the ordinary kernel.\ndef boundaryPrefix : Nat := 114258128115382768325149165979858622949054058922182384017825772718783752107996860734084690853574210578405379476224683606690194761257884644651583470255712858309128126\n\nset_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\ntheorem boundary_bits : ∀ t : Fin 545,\n    boundaryPrefix.testBit t = boundary gate31 t := by\n  decide\n\nset_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\ntheorem window_check : ∀ j : Fin 17,\n    (packedRun boundaryPrefix (528+j.val)).1.testBit 0 = false := by\n  decide\n\n/-- The seventeen white cells belong to the actual scalar reconstruction. -/\ntheorem seventeen_white (j : Nat) (hj : j < 17) :\n    recon (boundary gate31) (528+j) 0 = false := by\n  have h := (packed_sound boundaryPrefix 545 (boundary gate31)\n    (fun t ht => boundary_bits ⟨t,ht⟩) (528+j) 0 (by omega)).1\n  exact h.symm.trans (window_check ⟨j,hj⟩)\n\n/-- Spacing-three/five gates do not force a black initial cell in every\nseventeen-cell interval, even when the gate itself is periodic. -/\ntheorem no_uniform_gap_bound_sixteen :\n    ¬ (∀ G : Nat → Bool, (∀ r, G r = true → Next35 G r) →\n      ∀ n, 1 ≤ n → ∃ j, j ≤ 16 ∧ recon (boundary G) (n+j) 0 = true) := by\n  intro h\n  obtain ⟨j, hj, hb⟩ := h gate31 gate31_gaps 528 (by decide)\n  rw [seventeen_white j (by omega)] at hb\n  exact Bool.noConfusion hb\n\nend Rule30Submission.Gap\n",
  "ProjectDir" -> $Rule30PrizeKit, "IncludeInternal" -> True];
rule30KernelCheck = rule30Submission["Rule30Submission.Spacing.reconstruction_translate"]["KernelCheck"];
rule30KernelCheck
```

```wl
renormalizationHeadlines = {"Rule30Submission.Spacing.reconstruction_translate", "Rule30Submission.Spacing.transform_spaced_iff", "Rule30Submission.Spacing.second_translation_fails", "Rule30Submission.Gap.no_uniform_gap_bound_sixteen"};
Table[<|"Theorem" -> name, "Kind" -> rule30Submission[name]["Kind"],
  "Axioms" -> rule30Submission[name]["Axioms"]|>, {name, renormalizationHeadlines}]
```

The complete declaration replay and standard-axiom checks establish exactly
these partial claims. The universal sixteen-cell bound is negated directly in
`no_uniform_gap_bound_sixteen`. A passing partial headline check does not
establish an official prize target, and human review remains separate.
