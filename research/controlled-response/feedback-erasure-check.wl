(* Built-in full Rule 30 controls for the actual-feedback collision.
   Finite observations here accompany, and do not replace, the Lean proof. *)
ClearAll[feedbackErasureReport];
feedbackErasureReport[] := BlockRandom[
  SeedRandom[2026102406];
  Module[{cases},
    cases = Table[Module[{left, a, b, ca, cb, ha, hb, center = 8},
      left = If[sample == 1, ConstantArray[0, 9], Append[RandomInteger[1, 8], 0]];
      a = Join[left, {1,0}]; b = Join[left, {1,1}];
      ca = Flatten@CellularAutomaton[30, {a, 0}, {128, {{center}}}];
      cb = Flatten@CellularAutomaton[30, {b, 0}, {128, {{center}}}];
      ha = Flatten@CellularAutomaton[30, {a, 0}, {128, {{center+1}}}];
      hb = Flatten@CellularAutomaton[30, {b, 0}, {128, {{center+1}}}];
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
