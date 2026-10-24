(* Finite independent controls, not a replacement for the Lean proof. *)
ClearAll[quantitativeRankReport];
quantitativeRankReport[] := Module[{trace, shifted, cases},
  trace = Flatten@CellularAutomaton[30, {{1}, 0}, {2^12, {{0}}}];
  shifted = Rest[trace];
  cases = Table[Module[{h, flips},
    h = 2^m-1;
    flips = Total[(Boole[Unequal@@#]&) /@ Partition[Take[shifted, h+1], 2, 1]];
    <|"Exponent" -> m, "Horizon" -> h, "OuterRadius" -> 2^m+2,
      "ObservedFlips" -> flips, "DyadicLowerBoundHolds" -> (m <= flips)|>
  ], {m, 0, 12}];
  <|"FiniteSamplesOnly" -> True, "FullProblemClaim" -> False,
    "RankingConstructed" -> False, "CaseCount" -> Length[cases],
    "AllPassed" -> And@@Lookup[cases, "DyadicLowerBoundHolds"], "Cases" -> cases|>
];
