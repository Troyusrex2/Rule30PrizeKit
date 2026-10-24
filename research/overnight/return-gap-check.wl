(* Builtin CA30 controls for every tick of the saved return-score obstruction.
   This is not Lean verification or a prize result. *)
returnGapDir=DirectoryName[$InputFileName];
ClearAll[returnGapReport];
returnGapReport[]:=Module[{data,cert,cases,charges,dim,frame,maxima,vector,step,
    gains,reward=0,checks={},headChecks={},cells=0},
  data=Import[FileNameJoin[{returnGapDir,"seed-return-gap-rank-probe.json"}],"RawJSON"];
  cert=data["dual"];cases=cert["terms"];
  charges=Select[Tuples[{-1,0,1},4],Max[#]>0&];dim=6 Length[charges]+1;
  step[a_]:=BitXor[BitShiftLeft[a,2],BitOr[BitShiftLeft[a,1],a]];
  frame[a_,c_,d_]:=Module[{shift=IntegerExponent[a,2],primitive,width,m=d+1,ca,end},
    primitive=BitShiftRight[a,shift];width=IntegerLength[primitive,2];
    ca=CellularAutomaton[30,{Reverse[IntegerDigits[primitive,2]],0},m];
    end=BitShiftLeft[FromDigits[Reverse[Take[ca[[d+1]],
      {m-d+1,m-d+width+2 d}]],2],shift];
    {ca[[All,m+c-shift+1]],end,Times@@Dimensions[ca]}
  ];
  maxima[word_]:=Flatten[Transpose[Table[Module[{s,mins},
    s=Prepend[Accumulate[charge[[word+1]]],0];
    mins=FoldList[Min,First[s],Rest[s]];
    {Max[s],Last[s]-Min[s],Max[s-mins]}
  ],{charge,charges}]]];
  vector[a_,b_,c_]:=Module[{word,v,mode},
    word=Table[BitAnd[BitShiftRight[a,j],1]+2 BitAnd[BitShiftRight[b,j],1],
      {j,0,IntegerLength[a,2]-1}];
    v=Join[maxima[Take[word,c]],maxima[Drop[word,c+1]],{1}];
    mode=BitAnd[BitShiftRight[a,c],1];
    If[mode==0,Join[v,ConstantArray[0,dim]],Join[ConstantArray[0,dim],v]]
  ];
  gains=ConstantArray[0,2 dim];
  Do[Module[{a=FromDigits[s["outer"]],b=FromDigits[s["inner"]],c=s["center"],
      d=s["duration"],w=FromDigits[s["multiplier"]],x,y,rises},
    x=frame[a,c,d];y=frame[b,c,d];cells+=x[[3]]+y[[3]];
    AppendTo[checks,x[[2]]==Nest[step,a,d]&&y[[2]]==Nest[step,b,d]];
    rises=Flatten[Position[Partition[x[[1]],2,1],{0,1},{1}]]-1;
    AppendTo[headChecks,x[[1]]==y[[1]]&&rises=={0,d}];
    gains+=w (vector[x[[2]],y[[2]],c+d]-vector[a,b,c]);reward+=w
  ],{s,cases}];
  <|"LeanVerifiedByThisCalculation"->False,"FullProblemClaim"->False,
    "SeedOrbitRecheckedHere"->False,"CertificateReturns"->Length[cases],
    "BuiltinSpaceTimeFrames"->2 Length[cases],"BuiltinCellsCompared"->cells,
    "EveryMacroEndpointMatches"->And@@checks,
    "EveryTickAgreesAndReturnsAreConsecutive"->And@@headChecks,
    "AllWeightedFeatureGainsMatch"->(gains==(FromDigits/@cert["gains"])),
    "AllPassed"->(And@@checks&&And@@headChecks&&gains==(FromDigits/@cert["gains"])&&
      Min[gains]>=0&&reward==FromDigits[cert["weighted_reward"]]&&reward>0)|>
];
