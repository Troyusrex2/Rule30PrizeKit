(* Independent built-in CellularAutomaton checks. No Lean or submission claim. *)
ClearAll[globalTraceReport];
globalTraceReport[] := Module[{phi, packedTrace, caTrace, examples, rows, groups, widths},
  phi[n_Integer] := BitXor[n, BitOr[2 n,4 n]];
  packedTrace[n_,w_,h_] := MapIndexed[
    BitAnd[BitShiftRight[#1,w+First[#2]-1],1]&,NestList[phi,n,h-1]];
  (* CellularAutomaton aligns position 0 with the FIRST initial cell. *)
  caTrace[n_,w_,h_] := Flatten@CellularAutomaton[30,
    {IntegerDigits[n,2,2 w+1],0},{h-1,{{w}}}];
  examples = Map[Function[e, With[{a=e[[1]],b=e[[2]],w=e[[3]],h=e[[4]]},
    With[{ca=caTrace[a,w,h],cb=caTrace[b,w,h]},
      <|"rows"->{a,b},"width"->w,"observationLength"->h,
        "encodingChecks"->{SameQ[ca,packedTrace[a,w,h]],SameQ[cb,packedTrace[b,w,h]]},
        "firstDifference"->With[{p=FirstPosition[MapThread[Unequal,{ca,cb}],True]},
          If[MissingQ[p],Null,First[p]-1]]|>]]],
    {{2,3,1,1024},{329,337,7,256},{3487,3625,6,256},
     {19204870,8785767,12,256},{20110911,10934896,12,256}}];
  widths=Table[
    rows=Table[{caTrace[n,w,32],If[n==0,0,IntegerLength[n,2]]},{n,0,2^(2 w+1)-1}];
    <|"width"->w,"rows"->Length[rows],"minimumEdgeObservationLength"->
      SelectFirst[Range[0,32],Function[h,
        groups=GatherBy[rows,Take[First[#],h]&];
        AllTrue[groups,Length[DeleteDuplicates[#[[All,2]]]]==1&]]]|>,
    {w,0,4}];
  <|"finiteExperimentOnly"->True,"engineVersion"->$VersionNumber,
    "examples"->examples,"exhaustiveWidths"->widths|>
];
