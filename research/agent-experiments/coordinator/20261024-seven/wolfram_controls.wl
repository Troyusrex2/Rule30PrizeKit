(* Independent physical-frame CellularAutomaton control. No Cloud calls. *)
base = DirectoryName[$InputFileName];
phi[a_] := BitXor[a, BitOr[BitShiftLeft[a, 1], BitShiftLeft[a, 2]]];
packedTrace[a_, c_, n_] := MapIndexed[
  BitAnd[BitShiftRight[#1, c + First[#2] - 1], 1] &,
  NestList[phi, a, n - 1]];
physicalTrace[a_, c_, n_] := Module[{k = n + c + 8, init},
  init = Table[If[c - p >= 0, BitAnd[BitShiftRight[a, c - p], 1], 0], {p, -k, k}];
  CellularAutomaton[30, init, n - 1][[All, k + 1]]];
cases = {{48, 3, 28}, {49, 3, 28}, {33, 5, 60}, {46, 5, 60}, {1, 0, 128}};
checks = Map[Function[q, packedTrace @@ q === physicalTrace @@ q], cases];
If[!And @@ checks, Print["physical frame control failed"]; Exit[1]];
x = physicalTrace[48, 3, 28]; y = physicalTrace[49, 3, 28];
If[Take[x, 27] =!= Take[y, 27] || Last[x] === Last[y], Exit[2]];
m = {{{1, 1}, {0, 1}}, {{1, 1}, {1, 0}}};
v = {GoldenRatio, 1};
matrixChecks = Simplify[And @@ Flatten[Map[Thread[#.v <= GoldenRatio v] &, m]]];
If[matrixChecks =!= True, Exit[3]];
report = <|"version" -> $Version, "independentPhysicalFrameCases" -> cases,
  "allPhysicalControlsPassed" -> And @@ checks,
  "pair48_49EqualFirst27" -> True, "pair48_49DifferentAt27" -> True,
  "witnessMatricesCommonSubeigenvectorCheck" -> matrixChecks,
  "fullProblemSolved" -> False|>;
Export[FileNameJoin[{base, "wolfram-controls.json"}], report, "RawJSON"];
Print[ExportString[report, "RawJSON"]];
Exit[0];
