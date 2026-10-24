# An eight-column reconstruction identity and the limits of its iteration

Troy Lowry; OpenAI Codex • 2026-10-24

For a spaced boundary gate, Rule 30 sideways reconstruction translates eight columns by a simple gate transform. The spacing survives exactly when the original gate is white from index four onward. A period-five gate disproves unconditional iteration, and a period-31 spacing-three/five gate produces seventeen consecutive white initial cells. No prize problem or eventual period two is excluded.

## Scope and source

This essay is prepared for human review and has not been submitted to the prize API. It proves a partial structural identity and identifies two gaps in stronger extrapolations. It does not exclude eventual period two or solve a prize problem. No finite driven-right realization of the example gates is asserted.

The one-step identity follows the informal identity in [morpholib Theorem 14](https://github.com/fractastical/morpholib/blob/777865115483d310f72f0b9511b45409e330a8f5/docs/RULE30_PRIZE_SUBMISSION.md). That source is credited for the identity. The Lean formalization, support transfer, exact preservation criterion, packed-cone soundness theorem and counterexamples here were developed by Troy Lowry with OpenAI Codex. No claim of literature priority is made. The source's advertised global period-two elimination is not used as a premise.

## The identity and its required condition

Let b\_G(2r)=!G(r), b\_G(2r+1)=1 and D G(r)=G(r+2) xor G(r+4). Call G spaced when black cells never have distance one or two. For every spaced G, every m >= 1 and every time t, the kit's scalar reconstruction satisfies

recon b\_G (m+8) t = recon b\_(D G) m t.

An initial support bound W transfers to W-8. The preservation criterion is exact: D G is spaced if and only if G(r+4)=0 for every r. Thus this particular spacing hypothesis cannot be carried through a second step for an infinite gate. Other renormalizations remain possible.

## Independent finite observations

The following scalar reconstruction compares 12,800 cells. It also checks a period-five counterexample to applying the translation twice, and seventeen white initial cells at depths 528 through 544 for a period-31 gate whose black spacings are only three or five. These observations are independently connected to the kit's scalar reconstruction by Lean below.

```wl
In[1]:=
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
    "CellsCompared" -> Length[cases] * 40 * 64,
    "PeriodFiveInitialSpacing" -> And @@ Table[
      Not[g5[r] && g5[r + 1]] && Not[g5[r] && g5[r + 2]], {r, 0, 9}],
    "TransformedGateAtIndices1And3" -> {dg5[1], dg5[3]},
    "SecondTranslationDepth17Time0" -> mismatch,
    "SecondTranslationFails" -> Unequal @@ mismatch,
    "FullProblemClaim" -> False|>
];

ClearAll[spacingGapReport];
spacingGapReport[] := Module[{g, columns, whites},
  g = Function[r, MemberQ[{0, 3, 6, 9, 12, 15, 18, 21, 26}, Mod[r, 31]]];
  columns = spacingColumns[g, 544, 1];
  whites = Table[columns[[d + 1, 1]], {d, 528, 544}];
  <|"FiniteExperimentOnly" -> True, "GatePeriod" -> 31,
    "WhiteDepths" -> Range[528, 544], "ObservedCells" -> whites,
    "AllSeventeenWhite" -> And @@ (Not /@ whites),
    "GapConstraintCheckedAcrossTwoPeriods" -> And @@ Table[
      If[g[r], (!g[r + 1] && !g[r + 2] &&
        (g[r + 3] || (!g[r + 3] && !g[r + 4] && g[r + 5]))), True], {r, 0, 61}],
    "FiniteRightRealizabilityClaim" -> False, "FullProblemClaim" -> False|>
];

{spacingReport[], spacingGapReport[]}

Out[1]=  {<|"FiniteExperimentsOnly" -> True, "TranslationChecks" -> {True, True, True, True, True}, "CellsCompared" -> 12800, "PeriodFiveInitialSpacing" -> True, "TransformedGateAtIndices1And3" -> {True, True}, "SecondTranslationDepth17Time0" -> {False, Tru ... alse, False, False, False, False, False, False, False, False, False, False, False, False, False}, "AllSeventeenWhite" -> True, "GapConstraintCheckedAcrossTwoPeriods" -> True, "FiniteRightRealizabilityClaim" -> False, "FullProblemClaim" -> False|>}
```

The period-five example gives white at depth 17, time 0, where the twice transformed formula gives black. The period-31 example rules out a universal maximum white gap of sixteen under the spacing-three/five restriction alone. It does not rule out every larger gap bound.

## Exact embedded Lean source and full kernel replay

The code imports only the kit's core reconstruction and official statement modules. The packed-cone soundness theorem states its finite light-cone bound. The proof contains no new axioms, native decision procedure or custom elaborator.

```wl
In[2]:=
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit = Environment["RULE30PRIZE_KIT"];

In[3]:=
rule30Submission = LeanImportString["import Ruliology.CellularAutomata.Rule30ZeroBoundary
import Ruliology.CellularAutomata.Rule30Prize

open Ruliology.CellularAutomata

/-!
# An eight-column reconstruction identity and the condition needed to iterate it

The boundary history is `!G 0, 1, !G 1, 1, ...`. If the black gate
positions have spacing at least three, shifting reconstruction eight columns
left replaces `G r` by `G (r+2) xor G (r+4)`. This condition is not asserted
to hold after that replacement, or for every driven right half.
-/

namespace Rule30Submission.Spacing

open Rule30ZeroBoundary

def boundary (G : Nat → Bool) (t : Nat) : Bool :=
  if t % 2 = 0 then !G (t / 2) else true

def transform (G : Nat → Bool) (r : Nat) : Bool := xor (G (r+2)) (G (r+4))

def Spaced (G : Nat → Bool) : Prop :=
  ∀ r, (G r && G (r+1)) = false ∧ (G r && G (r+2)) = false

/-- The even/odd pair of a reconstructed column. -/
def pair (G : Nat → Bool) : Nat → Nat → Bool × Bool
  | 0, _ => (false, false)
  | 1, r => (!G r, true)
  | k+2, r =>
      (xor (pair G (k+1) r).2 ((pair G (k+1) r).1 || (pair G k r).1),
       xor (pair G (k+1) (r+1)).1 ((pair G (k+1) r).2 || (pair G k r).2))

theorem boundary_even (G : Nat → Bool) (r : Nat) : boundary G (2*r) = !G r := by
  simp [boundary, show 2*r % 2 = 0 by omega,
    show 2*r / 2 = r by omega]

theorem boundary_odd (G : Nat → Bool) (r : Nat) : boundary G (2*r+1) = true := by
  simp [boundary]

/-- The pair recurrence is exactly the kit's scalar reconstruction. -/
theorem pair_recon (G : Nat → Bool) : ∀ k r,
    pair G k r = (recon (boundary G) k (2*r), recon (boundary G) k (2*r+1))
  | 0, r => rfl
  | 1, r => by simp [pair, recon, boundary_even, boundary_odd]
  | k+2, r => by
      rw [pair, pair_recon G (k+1) r, pair_recon G (k+1) (r+1), pair_recon G k r]
      simp only [recon_two, show 2*r+1+1 = 2*(r+1) by omega]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ninth_pair (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 9 r = pair (transform G) 1 r := by
  have h0 := h r
  have h1 := h (r+1)
  have h2 := h (r+2)
  have h3 := h (r+3)
  simp only [Nat.add_assoc] at h1 h2 h3
  simp only [pair, transform, Nat.add_assoc]
  cases ha : G r <;> cases hb : G (r+1) <;> cases hc : G (r+2) <;>
    cases hd : G (r+3) <;> cases he : G (r+4) <;> simp_all

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tenth_pair (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 10 r = pair (transform G) 2 r := by
  have h0 := h r
  have h1 := h (r+1)
  have h2 := h (r+2)
  have h3 := h (r+3)
  have h4 := h (r+4)
  simp only [Nat.add_assoc] at h1 h2 h3 h4
  simp only [pair, transform, Nat.add_assoc]
  cases ha : G r <;> cases hb : G (r+1) <;> cases hc : G (r+2) <;>
    cases hd : G (r+3) <;> cases he : G (r+4) <;> cases hf : G (r+5) <;> simp_all

/-- An exact eight-column translation, with an explicit spacing premise. -/
theorem pair_translate (G : Nat → Bool) (h : Spaced G) : ∀ m r,
    pair G (m+9) r = pair (transform G) (m+1) r := by
  have key : ∀ m, (∀ r, pair G (m+9) r = pair (transform G) (m+1) r) ∧
      (∀ r, pair G (m+10) r = pair (transform G) (m+2) r) := by
    intro m
    induction m with
    | zero => exact ⟨ninth_pair G h, tenth_pair G h⟩
    | succ m ih =>
        refine ⟨ih.2, fun r => ?_⟩
        change
          (xor (pair G (m+10) r).2 ((pair G (m+10) r).1 || (pair G (m+9) r).1),
           xor (pair G (m+10) (r+1)).1 ((pair G (m+10) r).2 || (pair G (m+9) r).2)) =
          (xor (pair (transform G) (m+2) r).2
             ((pair (transform G) (m+2) r).1 || (pair (transform G) (m+1) r).1),
           xor (pair (transform G) (m+2) (r+1)).1
             ((pair (transform G) (m+2) r).2 || (pair (transform G) (m+1) r).2))
        rw [ih.2 r, ih.2 (r+1), ih.1 r]
  exact fun m => (key m).1

/-- The scalar statement holds at every time, not only at time zero. -/
theorem reconstruction_translate (G : Nat → Bool) (h : Spaced G) (m t : Nat) :
    recon (boundary G) (m+9) t = recon (boundary (transform G)) (m+1) t := by
  have hp := pair_translate G h m (t/2)
  rw [pair_recon, pair_recon] at hp
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht
  · have he : t = 2*(t/2) := by omega
    rw [he]
    exact congrArg Prod.fst hp
  · have he : t = 2*(t/2)+1 := by omega
    rw [he]
    exact congrArg Prod.snd hp

/-- An explicit support bound drops by eight under the translation. -/
theorem support_transfer (G : Nat → Bool) (h : Spaced G) (W : Nat)
    (hW : ∀ k, W < k → lam (boundary G) k = false) :
    ∀ k, W-8 < k → lam (boundary (transform G)) k = false := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m+1 := ⟨k-1, by omega⟩
  unfold lam
  rw [← reconstruction_translate G h]
  exact hW _ (by omega)

/-- A finite reconstructed initial row remains finite after the translation. -/
theorem finite_transfer (G : Nat → Bool) (h : Spaced G)
    (hf : FinSupp (lam (boundary G))) : FinSupp (lam (boundary (transform G))) := by
  obtain ⟨W, hW⟩ := hf
  exact ... r inverse rule.
The soundness bound explicitly excludes the unrepresented future boundary.
-/

namespace Rule30Submission.Packed

open Rule30ZeroBoundary Rule30Submission.Spacing

noncomputable def advance : Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat × Nat)
    (fun a b => (a,b))
    (fun _ ih a b => ih b (Nat.xor (Nat.shiftRight b 1) (Nat.lor b a)))

theorem advance_zero (a b : Nat) : advance 0 a b = (a,b) := rfl

theorem advance_succ (k a b : Nat) :
    advance (k+1) a b = advance k b ((b >>> 1) ^^^ (b ||| a)) := rfl

theorem advance_last : ∀ k a b,
    advance (k+1) a b =
      ((advance k a b).2,
       ((advance k a b).2 >>> 1) ^^^ ((advance k a b).2 ||| (advance k a b).1))
  | 0,a,b => rfl
  | k+1,a,b => by
      rw [advance_succ, advance_succ k a b, advance_last]

noncomputable def packedRun (B k : Nat) : Nat × Nat := advance k 0 B

theorem packedRun_zero (B : Nat) : packedRun B 0 = (0,B) := rfl

theorem packedRun_succ (B k : Nat) :
    packedRun B (k+1) =
      ((packedRun B k).2,
       ((packedRun B k).2 >>> 1) ^^^ ((packedRun B k).2 ||| (packedRun B k).1)) :=
  advance_last k 0 B

/-- Every checked bit agrees with scalar reconstruction inside its finite cone. -/
theorem packed_sound (B H : Nat) (b : Nat → Bool)
    (hb : ∀ t, t < H → B.testBit t = b t) : ∀ k t, t+k < H →
    (packedRun B k).1.testBit t = recon b k t ∧
    (packedRun B k).2.testBit t = recon b (k+1) t := by
  intro k
  induction k with
  | zero =>
      intro t ht
      exact ⟨by simp [packedRun_zero, recon], hb t ht⟩
  | succ k ih =>
      intro t ht
      have h0 := ih t (by omega)
      have h1 := ih (t+1) (by omega)
      rw [packedRun_succ]
      refine ⟨h0.2, ?_⟩
      simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight]
      rw [show 1+t=t+1 by omega, h1.2, h0.2, h0.1]
      exact (recon_two b k t).symm

end Rule30Submission.Packed

/-!
# A spacing-three/five gate with seventeen white initial cells

The gate is globally periodic of period 31, with gaps 3,3,3,3,3,3,3,5,5.
Its reconstructed initial row is white at depths 528 through 544. A finite
packed cone is proved equal to the kit's scalar reconstruction. There is no
claim that this gate is realized by a finite driven right half.
-/

namespace Rule30Submission.Gap

open Rule30ZeroBoundary Rule30Submission.Spacing
open Rule30Submission.Packed

def gate31 (r : Nat) : Bool := decide (r%31 ∈ [0,3,6,9,12,15,18,21,26])

def Next35 (G : Nat → Bool) (r : Nat) : Prop :=
  G (r+1) = false ∧ G (r+2) = false ∧
    (G (r+3) = true ∨ (G (r+3) = false ∧ G (r+4) = false ∧ G (r+5) = true))

theorem gate31_periodic (r : Nat) : gate31 (r+31) = gate31 r := by
  simp [gate31]

theorem gate31_residues : ∀ r : Fin 31, gate31 r = true → Next35 gate31 r := by
  unfold Next35
  decide

/-- Every black gate cell is followed by a gap of exactly three or five. -/
theorem gate31_gaps (r : Nat) (hr : gate31 r = true) : Next35 gate31 r := by
  have h := gate31_residues ⟨r%31, Nat.mod_lt r (by decide)⟩
  simp only [Next35, gate31, Nat.add_mod, Nat.mod_mod] at h hr ⊢
  exact h hr

theorem gate31_spaced : Spaced gate31 := by
  intro r
  cases hr : gate31 r with
  | false => simp
  | true =>
      have h := gate31_gaps r hr
      simp only [Next35] at h
      simp [h.1, h.2.1]

-- The finite boundary prefix is generated and cross-checked by the companion
-- Python experiment. Its bits are rechecked below by the ordinary kernel.
def boundaryPrefix : Nat := 114258128115382768325149165979858622949054058922182384017825772718783752107996860734084690853574210578405379476224683606690194761257884644651583470255712858309128126

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem boundary_bits : ∀ t : Fin 545,
    boundaryPrefix.testBit t = boundary gate31 t := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem window_check : ∀ j : Fin 17,
    (packedRun boundaryPrefix (528+j.val)).1.testBit 0 = false := by
  decide

/-- The seventeen white cells belong to the actual scalar reconstruction. -/
theorem seventeen_white (j : Nat) (hj : j < 17) :
    recon (boundary gate31) (528+j) 0 = false := by
  have h := (packed_sound boundaryPrefix 545 (boundary gate31)
    (fun t ht => boundary_bits ⟨t,ht⟩) (528+j) 0 (by omega)).1
  exact h.symm.trans (window_check ⟨j,hj⟩)

/-- Spacing-three/five gates do not force a black initial cell in every
seventeen-cell interval, even when the gate itself is periodic. -/
theorem no_uniform_gap_bound_sixteen :
    ¬ (∀ G : Nat → Bool, (∀ r, G r = true → Next35 G r) →
      ∀ n, 1 ≤ n → ∃ j, j ≤ 16 ∧ recon (boundary G) (n+j) 0 = true) := by
  intro h
  obtain ⟨j, hj, hb⟩ := h gate31 gate31_gaps 528 (by decide)
  rw [seventeen_white j (by omega)] at hb
  exact Bool.noConfusion hb

end Rule30Submission.Gap
",
  "ProjectDir" -> $Rule30PrizeKit, "IncludeInternal" -> True];
rule30KernelCheck = rule30Submission["Rule30Submission.Spacing.reconstruction_translate"]["KernelCheck"];
rule30KernelCheck

Out[3]=
Success["KernelChecked", Association["MessageTemplate" ->
   "The kernel accepts all `1` declarations of `2`.", "MessageParameters" ->
   {73, "LeanLinkTmp33396158764265443123x314511"},
  "Module" -> "LeanLinkTmp33396158764265443123x314511", "Declarations" -> 73]]

In[4]:=
renormalizationHeadlines = {"Rule30Submission.Spacing.reconstruction_translate", "Rule30Submission.Spacing.transform_spaced_iff", "Rule30Submission.Spacing.second_translation_fails", "Rule30Submission.Gap.no_uniform_gap_bound_sixteen"};
Table[<|"Theorem" -> name, "Kind" -> rule30Submission[name]["Kind"],
  "Axioms" -> rule30Submission[name]["Axioms"]|>, {name, renormalizationHeadlines}]

Out[4]=  {<|"Theorem" -> "Rule30Submission.Spacing.reconstruction_translate", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "propext"}|>, <|"Theorem" -> "Rule30Submission.Spacing.transform_spaced_iff", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "propext"}|>, <|"Theorem" -> "Rule30Submission.Spacing.second_translation_fails", "Kind" -> "theorem", "Axioms" -> {}|>, <|"Theorem" -> "Rule30Submission.Gap.no_uniform_gap_bound_sixteen", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "propext"}|>}
```

The complete declaration replay and standard-axiom checks establish exactly these partial claims. The universal sixteen-cell bound is negated directly in ``no_uniform_gap_bound_sixteen``. A passing partial headline check does not establish an official prize target, and human review remains separate.
