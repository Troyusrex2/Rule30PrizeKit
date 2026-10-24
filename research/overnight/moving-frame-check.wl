(* Finite independent controls; the unbounded statements are proved in Lean. *)
ClearAll[movingFrameReport];
movingFrameReport[] := Module[{h = 256, packed, ca, checks, periods, oddChecks},
  packed = NestList[BitXor[#, BitOr[BitShiftLeft[#, 1], BitShiftLeft[#, 2]]] &, 1, h];
  ca = CellularAutomaton[30, Join[ConstantArray[0, h+1], {1}, ConstantArray[0, h+1]], h];
  checks = Table[
    SameQ[IntegerDigits[packed[[t+1]], 2, 2*t+1], ca[[t+1, h+2-t ;; h+2+t]]],
    {t, 0, h}];
  periods = Table[Module[{p = 2^(k+1), bits, least},
    bits = Table[BitAnd[BitShiftRight[t+1, k], 1], {t, 0, 3*2^(k+1)-1}];
    least = SelectFirst[Range[p], Function[q,
      Take[bits, p] == Take[bits, {q+1, q+p}]]];
    <|"BitIndex" -> k, "ComputedLeastPeriod" -> least, "ExpectedPeriod" -> p,
      "Passed" -> SameQ[least, p]|>
  ], {k, 0, 7}];
  oddChecks = Table[BitAnd[BitShiftRight[2*t+1, t], 1] == 0, {t, 3, 1024}];
  <|"FiniteControlsOnly" -> True, "UnboundedProofReplaced" -> False,
    "FullProblemClaim" -> False, "MovingFrameOrigin" -> "right edge",
    "BuiltinRule30WholeRowsCompared" -> Length[checks],
    "AllWholeRowsPassed" -> And@@checks,
    "CounterPeriods" -> periods, "AllCounterPeriodChecksPassed" -> And@@Lookup[periods, "Passed"],
    "OddCounterDiagonalCases" -> Length[oddChecks], "OddCounterDiagonalAllWhite" -> And@@oddChecks|>
];
