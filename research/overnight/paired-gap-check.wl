(* Independent builtin CA30 and integer feature controls for gap-score certificates.
   This is not Lean verification or a prize solution. *)
gapCheckDir=DirectoryName[$InputFileName];
ClearAll[pairedGapReport];
pairedGapReport[]:=Module[{charges,dim,cellStep,packedStep,maxima,vector,results},
  charges=Select[Tuples[{-1,0,1},4],Max[#]>0&];
  dim=6 Length[charges]+1;
  (* Automatic CA cropping removes leading white cells. Restore their origin. *)
  cellStep[0]:=0;
  cellStep[a_]:=Module[{shift=IntegerExponent[a,2],primitive},
    primitive=BitShiftRight[a,shift];
    BitShiftLeft[FromDigits[Reverse[CellularAutomaton[30,
      {Reverse[IntegerDigits[primitive,2]],0},1][[2]]],2],shift]
  ];
  packedStep[a_]:=BitXor[BitShiftLeft[a,2],BitOr[BitShiftLeft[a,1],a]];
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
  results=Table[Module[{data,cert,cases,gains,reward=0,checks={},headChecks={},
      seedChecks={},cells=0,maxT,ca,pack,seed},
    data=Import[FileNameJoin[{gapCheckDir,name}],"RawJSON"];
    cert=data["dual"];cases=cert["terms"];seed=StringStartsQ[name,"seed-"];
    If[seed,
      maxT=Max[Lookup[cases,"center"]]+1;
      ca=CellularAutomaton[30,{{1},0},maxT];
      pack[t_]:=FromDigits[Reverse[Take[ca[[t+1]],{maxT-t+1,maxT+t+1}]],2]
    ];
    gains=ConstantArray[0,2 dim];
    Do[Module[{a=FromDigits[s["outer"]],b=FromDigits[s["inner"]],c=s["center"],
        w=FromDigits[s["multiplier"]],na,nb,oldMode,newMode,lag,t},
      na=cellStep[a];nb=cellStep[b];
      AppendTo[checks,na==packedStep[a]&&nb==packedStep[b]];
      cells+=IntegerLength[a,2]+IntegerLength[b,2]+4;
      oldMode=BitAnd[BitShiftRight[a,c],1];newMode=BitAnd[BitShiftRight[na,c+1],1];
      AppendTo[headChecks,oldMode==BitAnd[BitShiftRight[b,c],1]&&
        newMode==BitAnd[BitShiftRight[nb,c+1],1]];
      If[seed,lag=IntegerExponent[b,2];t=c-lag;
        AppendTo[seedChecks,a==pack[t+lag]&&b==BitShiftLeft[pack[t],lag]]];
      gains+=w (vector[na,nb,c+1]-vector[a,b,c]);
      reward+=w Boole[oldMode!=newMode]
    ],{s,cases}];
    <|"File"->name,"CertificateTerms"->Length[cases],"BuiltinOneStepRows"->2 Length[cases],
      "BuiltinOneStepCells"->cells,"ActualSeedCases"->If[seed,Length[cases],0],
      "BuiltinUpdatesMatch"->And@@checks,"HeadConditionsMatch"->And@@headChecks,
      "ActualSeedMatches"->And@@seedChecks,
      "WeightedGainsMatch"->(gains==(FromDigits/@cert["gains"])),
      "WeightedRewardMatches"->(reward==FromDigits[cert["weighted_reward"]]),
      "GainsNonnegative"->(Min[gains]>=0),
      "AllPassed"->(And@@checks&&And@@headChecks&&And@@seedChecks&&
        gains==(FromDigits/@cert["gains"])&&Min[gains]>=0&&
        reward==FromDigits[cert["weighted_reward"]]&&reward>0)|>
  ],{name,{"paired-gap-rank-probe.json","restart-gap-rank-probe.json","seed-gap-rank-probe.json"}}];
  <|"LeanVerifiedByThisCalculation"->False,"FullProblemClaim"->False,
    "FeatureDirections"->Length[charges],"Features"->2 dim,"Cases"->results,
    "LeadingWhiteOriginControlsPassed"->And@@Table[cellStep[a]==packedStep[a],
      {a,{0,1,2,3,4,5,8,9,13,32}}],
    "AllPassed"->(And@@Lookup[results,"AllPassed"]&&And@@Table[cellStep[a]==packedStep[a],
      {a,{0,1,2,3,4,5,8,9,13,32}}])|>
];
