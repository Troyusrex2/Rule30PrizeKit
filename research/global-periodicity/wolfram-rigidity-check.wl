ClearAll[rigidityReport];
rigidityReport[] := Module[{h=512,a,b,ca,cb,ia,ib,ja,jb,finite},
  a=Join[{1,0,1,0},Take[Flatten@ConstantArray[{0,1,0},Ceiling[(h-1)/3]],h-1]];
  b=Join[{1,1,0,0},Take[Flatten@ConstantArray[{1,0,0},Ceiling[(h-1)/3]],h-1]];
  ca=Flatten@CellularAutomaton[30,{a,0},{h-1,{{3}}}];
  cb=Flatten@CellularAutomaton[30,{b,0},{h-1,{{3}}}];
  ia=Flatten@CellularAutomaton[30,{a,0},{{1},{-1,8}}];
  ib=Flatten@CellularAutomaton[30,{b,0},{{1},{-1,8}}];
  ja=Flatten@CellularAutomaton[30,{a,0},{{2},{-2,8}}];
  jb=Flatten@CellularAutomaton[30,{b,0},{{2},{-2,8}}];
  finite=Join[{0,1},Flatten@CellularAutomaton[30,{{1,1,0,0,1,0},0},{h-3,{{5}}}]];
  <|"engineVersion"->$VersionNumber,"observationLength"->h,
    "finiteConeCrossCheckOnly"->True,"sameCenterTraceInCone"->SameQ[ca,cb],
    "differentInitialLeftNeighbor"->Unequal[a[[3]],b[[3]]],
    "firstImageWindowChecks"->{SameQ[ia,{1,1,0,1,1,1,1,1,1,1}],SameQ[ia,ib]},
    "secondImageWindowChecks"->{SameQ[ja,{1,1,0,0,1,0,0,0,0,0,0}],SameQ[ja,jb]},
    "finiteRowAfterTwoCheck"->SameQ[ca,finite],"tracePrefix"->Take[ca,24]|>
];
