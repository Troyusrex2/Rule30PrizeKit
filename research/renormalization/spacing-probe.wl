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
