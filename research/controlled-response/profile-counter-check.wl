(* Compare all three infinite profile tables with actual finite Rule 30 cones. *)
ClearAll[profileCounterReport];
profileCounterReport[] := Module[{tables, h = 32, window = 8, counts},
  tables = {{45,43,186,166,101,149,86,89},
    {42,45,51,170,170,85,170,85}, {85,87,168,212,172,178,202,43}};
  counts = Table[Module[{profile, n, initial, ca, checks},
    profile[k_] := table[[If[k<4, k+1, 5+Mod[k-4,4]]]];
    n = window+2*h+2;
    initial = Table[BitAnd[profile[k], 1], {k, 0, n-1}];
    ca = CellularAutomaton[30, Join[ConstantArray[0,h+1], initial, ConstantArray[0,h+1]], h];
    checks = Flatten@Table[
      ca[[t+1, h+2+k+t]] == BitAnd[BitShiftRight[profile[k], Mod[t,8]],1],
      {t,0,h}, {k,0,window-1}];
    <|"ScalarCellsCompared"->Length[checks], "AllPassed"->And@@checks|>
  ], {table,tables}];
  <|"FiniteControlsOnly"->True, "FullProblemClaim"->False,
    "BuiltinRule30Cones"->Length[counts], "Cases"->counts,
    "AllPassed"->And@@Lookup[counts,"AllPassed"]|>
];

ClearAll[profileCounterDiagram];
profileCounterDiagram[] := Module[{tables, labels},
  tables = {{45,43,186,166,101,149,86,89},
    {42,45,51,170,170,85,170,85}, {85,87,168,212,172,178,202,43}};
  labels = {"First OR example", "Second OR example", "Head period 2; state period 8"};
  GraphicsRow[Table[ArrayPlot[
    Table[BitAnd[BitShiftRight[tables[[j,If[k<4,k+1,5+Mod[k-4,4]]]],t],1],
      {t,0,7},{k,0,11}], ColorRules->{0->White,1->Black},
    Frame->True, FrameTicks->None, Mesh->All, MeshStyle->LightGray,
    PlotLabel->Style[labels[[j]],12],
    (* ArrayPlot orders these as {{bottom,top},{left,right}}. *)
    FrameLabel->{{"position 0 through 11",None},{"time 0 through 7 from top",None}},
    ImageSize->320], {j,3}], ImageSize->1050]
];
