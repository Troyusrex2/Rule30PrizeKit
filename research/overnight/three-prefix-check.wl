(* Independent built-in Rule 30 evolution with a prescribed 010 wall. *)
ClearAll[threePrefixReport];
threePrefixSamples = {{1146875464159318935777344604029556270007544, 0, 74}, {5102572859576143258559, 1, 5}, {60313895404792, 0, 26}, {2375971781484393678422915646712, 0, 23}, {244749599497708114625036297040031, 1, 35}, {344775886707615433983224, 0, 26}, {605216609138150171825374456, 0, 18}, {6727232044245249500500578204447114488, 0, 53}};
threePrefixReport[] := Module[{step,driver,ether,cases},
  step[x_,b_] := BitXor[BitShiftRight[x,1],BitOr[x,BitShiftLeft[x,1],b]];
  driver[t_] := Boole[Mod[t,3]==1];
  ether={{0,0,1},{0,0,1},{0,1,1},{1,1,0},{0,1,0},{0,1,0},
    {1,1,0},{1,0,1},{1,0,0},{1,0,0},{1,0,1},{0,1,1}};
  cases=Table[Module[{word=s[[1]],mode=s[[2]],d=s[[3]],h,w,pad,wall,ca,row,checks={},
      head={},referenceHead,cells=0},
    h=d+3;w=IntegerLength[word,2];pad=2*h+4;wall=pad+w+1;
    ca=Join[ConstantArray[0,pad],IntegerDigits[word,2],{driver[0]},ConstantArray[0,2*h+4]];
    row=word;
    referenceHead=ether[[If[mode==1,11,2]]];
    Do[
      AppendTo[head,BitAnd[row,1]];
      checks=Join[checks,Table[ca[[wall-1-k]]==BitAnd[BitShiftRight[row,k],1],{k,0,w+h-1}]];
      cells+=w+h;
      If[t<h,
        row=step[row,driver[t]];
        ca=Last[CellularAutomaton[30,ca,1]];
        ca[[wall]]=driver[t+1]
      ],{t,0,h}];
    <|"Mode"->mode,"FirstDefect"->d,"ScalarCellsCompared"->cells,
      "BuiltinConesMatch"->And@@checks,
      "NoEarlierHeadDifference"->And@@Table[head[[t+1]]==referenceHead[[Mod[t,3]+1]],{t,0,d-1}],
      "HeadFlipsAtFirstDefect"->(head[[d+1]]!=referenceHead[[Mod[d,3]+1]]),
      "FixedPhaseConstraintViolated"->If[Mod[d,3]==0,True,head[[d+1]]!=Boole[Mod[d,3]==2]]|>
  ],{s,threePrefixSamples}];
  <|"FiniteControlsOnly"->True,"LeanVerifiedByThisCalculation"->False,"FullProblemClaim"->False,
    "BuiltinRule30Cones"->Length[cases],"ScalarCellsCompared"->Total[Lookup[cases,"ScalarCellsCompared"]],
    "AllPassed"->(Length[cases]==8&&And@@Flatten[Lookup[cases,
      {"BuiltinConesMatch","NoEarlierHeadDifference","HeadFlipsAtFirstDefect","FixedPhaseConstraintViolated"}]]),
    "Cases"->cases|>
];
