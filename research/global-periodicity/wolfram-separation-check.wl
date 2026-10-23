ClearAll[separationReport];
separationReport[] := Module[{traces,results},
  traces[h_,m_] := DeleteDuplicates@Table[
    Flatten@CellularAutomaton[30,{IntegerDigits[a,2,h+m],0},{h-1,{{m}}}],
    {a,2^(h-1+m),2^(h+m)-1}];
  results=Map[Function[c,With[{h=c[[1]],m=c[[2]],n=c[[3]]},
    With[{a=traces[h,m],b=traces[h,n]},
      <|"horizon"->h,"leftDepths"->{m,n},"traceCounts"->{Length[a],Length[b]},
        "disjoint"->SameQ[Intersection[a,b],{}]|>]]],
    {{2,0,1},{3,0,2},{9,1,2},{3,1,1}}];
  <|"engineVersion"->$VersionNumber,"finiteConeEnumeration"->True,"results"->results|>
];
