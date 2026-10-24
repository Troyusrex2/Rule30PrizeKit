(* Finite independent controls; all-horizons statements are proved in Lean. *)
ClearAll[pairedTraceReport];
pairedTraceReport[] := <|
  "FiniteSamplesOnly" -> True, "FullProblemClaim" -> False,
  "Results" -> Table[Module[{n, a, b, ca, cb},
    n = h+3;
    a = Table[Boole[MemberQ[{-n,-1,0,1,n},p]], {p,-n,n}];
    b = Table[Boole[MemberQ[{-1,0,1},p]], {p,-n,n}];
    ca = Flatten@CellularAutomaton[30,{a,0},{h,{{n}}}];
    cb = Flatten@CellularAutomaton[30,{b,0},{h,{{n}}}];
    <|"Horizon" -> h, "ObservationCount" -> Length[ca],
      "InitialBlackCounts" -> {Total[a],Total[b]}, "SameCenterPrefix" -> SameQ[ca,cb],
      "StrictlyNestedSupports" -> (n>1)|>
  ],{h,{0,1,2,8,32,128,512,1024}}]
|>;
