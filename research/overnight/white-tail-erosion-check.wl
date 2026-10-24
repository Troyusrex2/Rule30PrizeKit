(* A periodic array with margins isolates a genuine full Rule 30 causal cone.
   Up to the first prefix departure, its boundary remains the matching ether.
   It is not claimed to reproduce a forced boundary after that departure. *)
ClearAll[whiteTailErosionReport];
whiteTailErosionReport[path_String] := Module[{data,cols,eth,advance,cases},
  data=Import[path,"RawJSON"];
  cols=IntegerDigits[FromDigits[#,2],2,3]& /@
    {"001","001","011","110","010","010","110","101","100","100","101","011"};
  eth[j_,t_] := cols[[Mod[j,12]+1,Mod[t,3]+1]];
  advance[a_,b_] := BitXor[BitOr[BitShiftLeft[a,1],b],BitOr[a,BitShiftRight[a,1]]];
  cases=Table[Module[{j=c["attachment"],phase=c["phase"],k=c["prefix"],
      w=c["support_bound"],word=FromDigits[c["initial_right_word"]],
      d=c["first_departure"],left,initial,ca,rows,first,ok,cells=0},
    left=d+3;
    initial=Join[Table[eth[j+p,phase],{p,-left,0}],
      Reverse[IntegerDigits[word,2,w]],ConstantArray[0,2*d+4]];
    ca=CellularAutomaton[30,initial,d];
    rows=FoldList[advance[#1,eth[j,#2+phase]]&,word,Range[0,d-1]];
    first=SelectFirst[Range[0,d],Function[t,
      AnyTrue[Range[1,k],Function[p,
        BitAnd[BitShiftRight[rows[[t+1]],p-1],1]!=eth[j+p,t+phase]]]],Missing["None"]];
    ok=And@@Flatten@Table[
      cells++;
      ca[[t+1,left+1+p]]==If[p==0,eth[j,t+phase],
        BitAnd[BitShiftRight[rows[[t+1]],p-1],1]],{t,0,d},{p,0,w+t+1}];
    <|"Attachment"->j,"Phase"->phase,"Prefix"->k,"SupportBound"->w,
      "FirstDeparture"->first,"ExpectedFirstDeparture"->d,
      "DepartureMatchesPython"->(first===d),
      "BuiltinConeMatchesDrivenHalfUntilDeparture"->ok,
      "ScalarCellsCompared"->cells,
      "SupportBoundHolds"->And@@Table[BitShiftRight[rows[[t+1]],w+t]==0,{t,0,d}],
      "ErosionBoundHolds"->(IntegerQ[first]&&first<=c["proposed_bound"])|>
  ],{c,data["cases"]}];
  <|"FiniteControlsOnly"->True,"LeanVerifiedByThisCalculation"->False,
    "FullProblemClaim"->False,"Cases"->cases,"BuiltinRule30Cones"->Length[cases],
    "ScalarCellsCompared"->Total[Lookup[cases,"ScalarCellsCompared"]],
    "AllPassed"->And@@Flatten[Lookup[cases,{"DepartureMatchesPython",
      "BuiltinConeMatchesDrivenHalfUntilDeparture","SupportBoundHolds","ErosionBoundHolds"}]]|>
];
