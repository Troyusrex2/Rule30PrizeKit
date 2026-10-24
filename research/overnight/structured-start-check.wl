(* Independent builtin CA30 control for finite prescribed-trace starts.
   This finite calculation is not a Lean proof or an infinite construction. *)
structuredCheckDir=DirectoryName[$InputFileName];
ClearAll[structuredStartReport];
structuredStartReport[]:=Module[{cases,results},
  cases=Import[FileNameJoin[{structuredCheckDir,"structured-start-cases.json"}],"RawJSON"];
  results=Table[Module[{n=s["depth"],a=FromDigits[s["row"]],c=s["center"],
      digits,ca,rows,step,packed,tops,width},
    width=IntegerLength[a,2];digits=Reverse[IntegerDigits[a,2]];
    ca=CellularAutomaton[30,{digits,0},n];
    step[x_]:=BitXor[BitShiftLeft[x,2],BitOr[BitShiftLeft[x,1],x]];
    rows=NestList[step,a,n];
    packed=Table[FromDigits[Reverse[Take[ca[[t+1]],{n-t+1,n-t+width+2*t}]],2],{t,0,n}];
    tops=Table[ca[[t+1,n+c+1]]==Boole[EvenQ[t]],{t,0,n}];
    <|"Depth"->n,"RightInitial"->s["right_initial"],"InitialWidth"->width,
      "BuiltinRowsMatchPacked"->(packed==rows),
      "EveryRequestedCenterBitMatches"->And@@tops,
      "Observations"->Length[tops],"CellsCompared"->Total[width+2*Range[0,n]]|>
  ],{s,cases}];
  <|"LeanVerifiedByThisCalculation"->False,"FullProblemClaim"->False,
    "Cases"->results,"AllPassed"->And@@Flatten[Lookup[results,
      {"BuiltinRowsMatchPacked","EveryRequestedCenterBitMatches"}]]|>
];
