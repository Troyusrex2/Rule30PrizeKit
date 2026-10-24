> Reading export from the evaluated notebook. The notebook reader abbreviates long input and output cells; the complete proof is in [Rule30RenormalizationStandalone.lean](Rule30RenormalizationStandalone.lean).

# Empty-right gate spacing and the limits of reconstruction iteration

Troy Lowry; OpenAI Codex • 2026-10-24

A certified 16-cell forward invariant proves exact spacings three or five in the empty-right driven gate from white cycle 146 onward. Its eight-column reconstruction translation applies once, but the required spacing fails after transformation. Two checked examples also refute unconditional iteration and a universal sixteen-cell white-gap bound. The reconstructed left row is not proved infinite, and no prize problem or eventual period two is excluded.

## Scope and source

This essay is prepared for human review and has not been submitted to the prize API. It proves an unbounded driven-gate spacing theorem, a structural identity, and exact obstructions to stronger extrapolations. It does not prove CQ01Empty, exclude eventual period two or solve a prize problem. The empty-right gate is realized by the actual driven system; no finite-right realization of the separate period-five or period-31 example gates is asserted.

The one-step identity follows the informal identity in [morpholib Theorem 14](https://github.com/fractastical/morpholib/blob/777865115483d310f72f0b9511b45409e330a8f5/docs/RULE30_PRIZE_SUBMISSION.md). That source is credited for the identity. The Lean formalization, support transfer, exact preservation criterion, packed-cone soundness theorem and counterexamples here were developed by Troy Lowry with OpenAI Codex. No claim of literature priority is made. The source's advertised global period-two elimination is not used as a premise.

## The identity and its required condition

Let b\_G(2r)=!G(r), b\_G(2r+1)=1 and D G(r)=G(r+2) xor G(r+4). Call G spaced when black cells never have distance one or two. For every spaced G, every m >= 1 and every time t, the kit's scalar reconstruction satisfies

recon b\_G (m+8) t = recon b\_(D G) m t.

An initial support bound W transfers to W-8. The preservation criterion is exact: D G is spaced if and only if G(r+4)=0 for every r. Thus this particular spacing hypothesis cannot be carried through a second step for an infinite gate. Other renormalizations remain possible.

## The actual empty-right gate

Let u(s) be position one at physical time 2s+1 of the right half driven by an alternating black-first center, starting with an entirely white right half. Set G(r)=u(146+r). A forward invariant of 13,937 sixteen-cell prefixes contains the actual prefix at physical time 293. The certificate checks all 262,144 eighteen-bit cases, including every possibility for the two unseen right cells. It checks both closure and six-cycle gate observations. Induction therefore proves, at every later time, that black observations are separated by exactly three or five cycles, and that no six-cycle gate window is all white.

The packed engine is proved equal to the kit's driven evolution, with explicit tail-dependence lemmas. The search that generated the wall is untrusted; every certificate case is checked by ordinary kernel reduction. There are no native decision procedures or added axioms.

The translation applies once to this actual spaced gate. Its transform is provably not spaced, so the same lemma cannot be iterated on it. Infinitely many black gate observations do not establish infinitely many black cells in the reconstructed initial left row. That remaining assertion is CQ01Empty, which this essay leaves open.

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

import Ruliology.CellularAutomata.Rule30PeriodTwoSideways

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
    (hf : FinSupp (lam (boundary G))) : FinSupp (lam (bo ... lock203
  | 204,_ => block204
  | 205,_ => block205
  | 206,_ => block206
  | 207,_ => block207
  | 208,_ => block208
  | 209,_ => block209
  | 210,_ => block210
  | 211,_ => block211
  | 212,_ => block212
  | 213,_ => block213
  | 214,_ => block214
  | 215,_ => block215
  | 216,_ => block216
  | 217,_ => block217
  | 218,_ => block218
  | 219,_ => block219
  | 220,_ => block220
  | 221,_ => block221
  | 222,_ => block222
  | 223,_ => block223
  | 224,_ => block224
  | 225,_ => block225
  | 226,_ => block226
  | 227,_ => block227
  | 228,_ => block228
  | 229,_ => block229
  | 230,_ => block230
  | 231,_ => block231
  | 232,_ => block232
  | 233,_ => block233
  | 234,_ => block234
  | 235,_ => block235
  | 236,_ => block236
  | 237,_ => block237
  | 238,_ => block238
  | 239,_ => block239
  | 240,_ => block240
  | 241,_ => block241
  | 242,_ => block242
  | 243,_ => block243
  | 244,_ => block244
  | 245,_ => block245
  | 246,_ => block246
  | 247,_ => block247
  | 248,_ => block248
  | 249,_ => block249
  | 250,_ => block250
  | 251,_ => block251
  | 252,_ => block252
  | 253,_ => block253
  | 254,_ => block254
  | 255,_ => block255
  | n+256,h => by omega

theorem good_all (q : Nat) (hq : q<262144) : Good q := by
  have hb := all_blocks (q/1024) (by omega)
  have he := (List.all_eq_true.mp hb) (q%1024) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hh : 1024*(q/1024)+q%1024=q := by omega
  rw [hh] at he
  exact of_decide_eq_true he

theorem entry : wall (white 146)=true := by decide

end Rule30Submission.DrivenWall

/-!
# Eventual spacings three or five in the empty-right driven gate

This is a certified forward invariant of the driven right half, not a proof
that its reconstructed left row is infinite. In particular it does not prove
`CQ01Empty`, `CQ01`, `Q01`, or any prize problem.
-/

namespace Rule30Submission.EmptyGate

open Rule30Submission.Driven Rule30Submission.DrivenWall
open Rule30PeriodTwoSideways Rule30Submission.Spacing

theorem wall_trim (a : Nat) : wall (a % 2^18)=wall a := by
  unfold wall
  rw [Nat.mod_mod_of_dvd a (by decide : 65536 ∣ 2^18)]

/-- The two unseen right cells range over every possibility in `good_all`. -/
theorem wall_step (a : Nat) (ha : wall a=true) : Observe a ∧ wall (double a)=true := by
  have ht : wall (a % 262144)=true := by
    change wall (a % 2^18)=true
    rw [wall_trim]
    exact ha
  have hg := good_all (a%262144) (Nat.mod_lt _ (by decide)) ht
  refine ⟨(observe_trim a).mp hg.1,?_⟩
  have he : wall (double (a % 2^18))=wall (double a) := by
    unfold wall
    rw [← double_prefix a 16]
  rw [he] at hg
  exact hg.2

theorem white_wall : ∀ n, wall (white (146+n))=true
  | 0 => entry
  | n+1 => by
      rw [show 146+(n+1)=(146+n)+1 by omega,white]
      exact (wall_step _ (white_wall n)).2

def gate (r : Nat) : Bool := u empty (146+r)

/-- Every six-cycle window obeys the exact gate restrictions, at all later times. -/
theorem empty_windows (r : Nat) : Window gate r := by
  have ho := (wall_step _ (white_wall r)).1
  simpa only [Observe,Window,gate,Nat.zero_add,Nat.add_zero,iterate_white,white_gate,Nat.add_assoc] using ho

/-- Black gate positions are never separated by one or two cycles. -/
theorem empty_spaced : Spaced gate := by
  intro r
  exact ⟨(empty_windows r).1,(empty_windows r).2.1⟩

/-- After a black observation, the next black observation is exactly three or five cycles later. -/
theorem empty_next_gap (r : Nat) (hr : gate r=true) :
    (gate (r+3)=true ∧ gate (r+4)=false ∧ gate (r+5)=false) ∨
    (gate (r+3)=false ∧ gate (r+4)=false ∧ gate (r+5)=true) :=
  (empty_windows r).2.2.1 hr

theorem empty_no_six_white (r : Nat) :
    (gate r || gate (r+1) || gate (r+2) || gate (r+3) || gate (r+4) || gate (r+5))=true :=
  (empty_windows r).2.2.2

theorem empty_black_after (r : Nat) : ∃ s, r≤s ∧ gate s=true := by
  have h := empty_no_six_white r
  simp only [Bool.or_eq_true] at h
  rcases h with ((((ha | hb) | hc) | hd) | he) | hf
  · exact ⟨r,Nat.le_refl _,ha⟩
  · exact ⟨r+1,by omega,hb⟩
  · exact ⟨r+2,by omega,hc⟩
  · exact ⟨r+3,by omega,hd⟩
  · exact ⟨r+4,by omega,he⟩
  · exact ⟨r+5,by omega,hf⟩

/-- The previously formalized translation applies once to this actual driven gate. -/
theorem empty_reconstruction_translate (m t : Nat) :
    Rule30ZeroBoundary.recon (boundary gate) (m+9) t =
      Rule30ZeroBoundary.recon (boundary (transform gate)) (m+1) t :=
  reconstruction_translate gate empty_spaced m t

/-- The one-step reconstruction transform still cannot be iterated on this actual driven gate. -/
theorem transformed_empty_not_spaced : ¬ Spaced (transform gate) := by
  intro h
  have hz := (transform_spaced_iff gate empty_spaced).mp h
  have hw := empty_no_six_white 4
  rw [hz 0,hz 1,hz 2,hz 3,hz 4,hz 5] at hw
  contradiction

end Rule30Submission.EmptyGate
",
  "ProjectDir" -> $Rule30PrizeKit, "IncludeInternal" -> True];
rule30KernelCheck = rule30Submission["Rule30Submission.Spacing.reconstruction_translate"]["KernelCheck"];
rule30KernelCheck

Out[3]=
Success["KernelChecked", Association["MessageTemplate" ->
   "The kernel accepts all `1` declarations of `2`.", "MessageParameters" ->
   {424, "LeanLinkTmp33396184375944630536x139800"},
  "Module" -> "LeanLinkTmp33396184375944630536x139800", "Declarations" -> 424]]

In[4]:=
renormalizationHeadlines = {"Rule30Submission.Spacing.reconstruction_translate", "Rule30Submission.Spacing.transform_spaced_iff", "Rule30Submission.Spacing.second_translation_fails", "Rule30Submission.Gap.no_uniform_gap_bound_sixteen", "Rule30Submission.EmptyGate.empty_spaced", "Rule30Submission.EmptyGate.empty_next_gap", "Rule30Submission.EmptyGate.transformed_empty_not_spaced"};
Table[<|"Theorem" -> name, "Kind" -> rule30Submission[name]["Kind"],
  "Axioms" -> rule30Submission[name]["Axioms"]|>, {name, renormalizationHeadlines}]

Out[4]=  {<|"Theorem" -> "Rule30Submission.Spacing.reconstruction_translate", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "propext"}|>, <|"Theorem" -> "Rule30Submission.Spacing.transform_spaced_iff", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "prop ... " -> "Rule30Submission.EmptyGate.empty_next_gap", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "propext"}|>, <|"Theorem" -> "Rule30Submission.EmptyGate.transformed_empty_not_spaced", "Kind" -> "theorem", "Axioms" -> {"Quot.sound", "propext"}|>}
```

The complete declaration replay and standard-axiom checks establish exactly these partial claims. The universal sixteen-cell bound is negated directly in ``no_uniform_gap_bound_sixteen``. A passing partial headline check does not establish an official prize target, and human review remains separate.
