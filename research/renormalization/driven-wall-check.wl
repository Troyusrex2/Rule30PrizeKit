(* Independent finite checks. The unbounded claim belongs to Lean, not this script. *)
ClearAll[wallDouble, wallVectorStep, wallPrefix, drivenWallReport];
wallDouble[x_Integer] := Module[{half},
  half = BitXor[BitShiftLeft[x, 1], BitOr[x, BitShiftRight[x, 1]]];
  BitXor[BitOr[BitShiftLeft[half, 1], 1], BitOr[half, BitShiftRight[half, 1]]]
];
wallVectorStep[v_List, b_Integer] := MapThread[
  Function[{l, c, r}, BitXor[l, BitOr[c, r]]],
  {Prepend[Most[v], b], v, Append[Rest[v], 0]}];
wallPrefix[v_List] := Take[v, 16].(2^Range[0, 15]);
drivenWallReport[source_String] := Module[
  {hex, mask, safe, states, closure, observations, controls, samples, row, entries,
   firstEntry, prefix, result, elapsed},
  {elapsed, result} = AbsoluteTiming[
    hex = First[StringCases[Import[source, "Text"], RegularExpression["0x[0-9a-f]+"]]];
    mask = FromDigits[StringDrop[hex, 2], 16];
    safe[q_Integer] := BitAnd[BitShiftRight[mask, BitAnd[q, 65535]], 1] == 1;
    states = Select[Range[0, 65535], safe];
    closure = And @@ Flatten[Table[
      safe[wallDouble[q + tail*65536]], {q, states}, {tail, 0, 3}]];
    observations = And @@ Table[Module[{bits},
      bits = BitAnd[#, 1] & /@ NestList[wallDouble, q, 5];
      MemberQ[{2, 4, 8, 9, 16, 18, 33, 34, 36}, bits.(2^Range[0, 5])]], {q, states}];
    samples = Mod[Range[0, 255]*104729 + 17, 262144];
    controls = And @@ Table[
      wallPrefix[wallVectorStep[wallVectorStep[Reverse[IntegerDigits[q, 2, 18]], 0], 1]] ==
        BitAnd[wallDouble[q], 65535], {q, samples}];
    row = ConstantArray[0, 320]; entries = {};
    Do[row = wallVectorStep[row, Boole[EvenQ[t]]];
      If[EvenQ[t], AppendTo[entries, safe[wallPrefix[row]]]], {t, 0, 292}];
    firstEntry = FirstPosition[entries, True][[1]] - 1;
    prefix = wallPrefix[row];
    <|"FiniteChecksOnly" -> True, "FullProblemClaim" -> False,
      "SafeStates" -> Length[states], "AllTailTransitions" -> 4 Length[states],
      "Closed" -> closure, "AllGateWindows" -> observations,
      "IndependentVectorControls" -> Length[samples], "VectorControlsPass" -> controls,
      "EmptyFirstEntryWhiteCycle" -> firstEntry, "EmptyEntryPhysicalTime" -> 293,
      "EmptyEntryPrefix" -> prefix|>
  ];
  Append[result, "Seconds" -> elapsed]
];
