(* Finite controls using independent built-in Rule 30 causal cones. *)
ClearAll[finiteClock16Report];
finiteClock16SampleWords = {1071292029505993517027974728227441735014801995855195223534253,3148244321913096809142,1650586719047173699865498955,9514984618039732540388573129663300909218310819,2043327387821185144477796036200412244824985496244802899,5230918112822233969863157852673055346751962870386695427400,15011998757901638,31178701596392595588345276431280704419326560916806};
finiteClock16Report[] := Module[{words=finiteClock16SampleWords,q,h=32,cases},
  q[x_] := BitXor[x,BitOr[BitShiftRight[x,1],BitShiftRight[x,2]]];
  cases=Table[Module[{w=IntegerLength[a,2],initial,ca,iter,checks,head,hs},
    initial=Join[ConstantArray[0,h+1],Reverse[IntegerDigits[a,2]],ConstantArray[0,3*h+1]];
    ca=CellularAutomaton[30,initial,h];iter=NestList[q,a,h];
    checks=Flatten@Table[ca[[t+1,h+2+k+t]]==BitAnd[BitShiftRight[iter[[t+1]],k],1],
      {t,0,h},{k,0,w-1}];
    head=BitAnd[#,1]& /@ Take[iter,16];
    hs=Select[Range[0,15],RotateLeft[head,#]===head&];
    <|"Width"->w,"FullClockReturns"->(iter[[17]]==a),"ScalarCellsCompared"->Length[checks],
      "BuiltinConeMatchesQ"->And@@checks,
      "HeadClocksDetected"->And@@Table[iter[[H+1]]==a,{H,hs}]|>
  ],{a,words}];
  <|"FiniteControlsOnly"->True,"LeanVerifiedByThisCalculation"->False,
    "FullProblemClaim"->False,"BuiltinRule30Cones"->Length[cases],
    "ScalarCellsCompared"->Total[Lookup[cases,"ScalarCellsCompared"]],
    "AllPassed"->And@@Flatten[Lookup[cases,{"FullClockReturns","BuiltinConeMatchesQ","HeadClocksDetected"}]],
    "Cases"->cases|>
];
