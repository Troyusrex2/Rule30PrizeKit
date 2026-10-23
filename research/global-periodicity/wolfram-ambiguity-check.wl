ClearAll[finiteAmbiguityReport];
finiteAmbiguityReport[] := <|
  "engineVersion" -> $VersionNumber,
  "finiteSamplesOnly" -> True,
  "allHorizonsTheoremRequiresLean" -> True,
  "results" -> Table[Module[{a,b,ca,cb},
    a=Join[{1,0,1,0},Take[Flatten@ConstantArray[{0,1,0},Ceiling[h/3]],h]];
    b=Join[{1,1,0,0},Take[Flatten@ConstantArray[{1,0,0},Ceiling[h/3]],h]];
    ca=If[h==0,{},Flatten@CellularAutomaton[30,{a,0},{h-1,{{3}}}]];
    cb=If[h==0,{},Flatten@CellularAutomaton[30,{b,0},{h-1,{{3}}}]];
    <|"observationLength"->h,"initialSupportWindow"->{-3,h},
      "sameCenterPrefix"->SameQ[ca,cb],
      "differentInitialLeftNeighbor"->Unequal[a[[3]],b[[3]]],
      "bothLeftEdgesMinusThree"->SameQ[{a[[1]],b[[1]]},{1,1}]|>
  ],{h,{0,1,2,9,32,128,512,1024}}]
|>;
