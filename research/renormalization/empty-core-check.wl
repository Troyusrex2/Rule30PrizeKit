(* Independent finite controls; Lean supplies the all-time induction. *)
ClearAll[coreDouble, coreVectorStep, corePrefix, emptyCoreReport];
coreDouble[x_Integer] := Module[{half},
  half = BitXor[BitShiftLeft[x, 1], BitOr[x, BitShiftRight[x, 1]]];
  BitXor[BitOr[BitShiftLeft[half, 1], 1], BitOr[half, BitShiftRight[half, 1]]]
];
coreVectorStep[v_List, b_Integer] := MapThread[
  Function[{l, c, r}, BitXor[l, BitOr[c, r]]],
  {Prepend[Most[v], b], v, Append[Rest[v], 0]}];
corePrefix[v_List] := Take[v, 16].(2^Range[0, 15]);
emptyCoreReport[source_String] := Module[
  {hex, mask, safe, states, closure, observations, controls, samples, row,
   entries, firstEntry, prefix, result, elapsed},
  {elapsed, result} = AbsoluteTiming[
    hex = First[StringCases[Import[source, "Text"], RegularExpression["0x[0-9a-f]+"]]];
    mask = FromDigits[StringDrop[hex, 2], 16];
    safe[q_Integer] := BitAnd[BitShiftRight[mask, BitAnd[q, 65535]], 1] == 1;
    states = Select[Range[0, 65535], safe];
    closure = And @@ Flatten[Table[
      safe[coreDouble[q + tail*65536]], {q, states}, {tail, 0, 3}]];
    observations = And @@ Table[Module[{bits},
      bits = BitAnd[#, 1] & /@ NestList[coreDouble, q, 7];
      MemberQ[{8, 9, 16, 18, 33, 36, 66, 72, 132, 144}, bits.(2^Range[0, 7])] &&
        bits[[1]] bits[[4]] bits[[7]] == 0], {q, states}];
    samples = Mod[Range[0, 255]*104729 + 17, 262144];
    controls = And @@ Table[
      corePrefix[coreVectorStep[coreVectorStep[Reverse[IntegerDigits[q, 2, 18]], 0], 1]] ==
        BitAnd[coreDouble[q], 65535], {q, samples}];
    row = ConstantArray[0, 340]; entries = {};
    Do[row = coreVectorStep[row, Boole[EvenQ[t]]];
      If[EvenQ[t], AppendTo[entries, safe[corePrefix[row]]]], {t, 0, 310}];
    firstEntry = FirstPosition[entries, True][[1]] - 1;
    prefix = corePrefix[row];
    <|"FiniteChecksOnly" -> True, "FullProblemClaim" -> False,
      "CoreStates" -> Length[states], "AllTailTransitions" -> 4 Length[states],
      "Closed" -> closure, "AllGateWindows" -> observations,
      "IndependentVectorControls" -> Length[samples], "VectorControlsPass" -> controls,
      "EmptyFirstEntryWhiteCycle" -> firstEntry, "EmptyEntryPhysicalTime" -> 311,
      "EmptyEntryPrefix" -> prefix|>
  ];
  Append[result, "Seconds" -> elapsed]
];
