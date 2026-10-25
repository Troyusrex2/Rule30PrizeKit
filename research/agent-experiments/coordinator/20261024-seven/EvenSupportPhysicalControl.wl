(* Independent scalar-list Rule 30 evolution with a clamped white wall.
   These are mathematical test inputs, not machine configuration values. *)
ClearAll[zStep, decodeEven];
zStep[row_List] := MapThread[BitXor, {
  Append[Rest[row], 0],
  MapThread[BitOr, {row, Prepend[Most[row], 0]}]
}];
decodeEven[u_Integer, n_Integer] := Module[{row, free, d, head},
  row = ConstantArray[0, 2 n + 2]; free = ConstantArray[0, n];
  Do[
    head = First[Nest[zStep, row, 2 d]];
    row[[2 d + 1]] = 1 - head;
    row[[2 d + 2]] = BitAnd[BitShiftRight[u, d], 1];
    free[[d + 1]] = First[Nest[zStep, row, 2 d + 1]],
    {d, 0, n - 1}
  ];
  <|"even_input" -> u, "free_bits" -> free|>
];
result = TimeConstrained[
  <|"engine" -> $Version, "method" -> "scalar list Rule 30 with white wall",
    "free_prefix_length" -> 24, "cases" -> Table[decodeEven[u, 24], {u, 0, 31}],
    "Lean_premise" -> False|>, 200, $Failed
];
If[result === $Failed, Print["CONTROL TIMEOUT"]; Exit[1]];
Export[FileNameJoin[{DirectoryName[$InputFileName], "even-support-wolfram-control.json"}], result, "RawJSON"];
Print["Wolfram scalar controls exported: 32 cases"];
Exit[0];
