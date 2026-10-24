(* Independent built-in Rule 30 cones for both tails. *)
ClearAll[terminalClockReport];
terminalClockReport[] := Module[{q,h=48,cases,samples},
  q[x_] := BitXor[x,BitOr[BitShiftRight[x,1],BitShiftRight[x,2]]];
  samples={{0,0,0},{0,0,1},{1,1,0},{7,93,1},{16,52311,0},
    {32,3687745881,1},{64,17644052093809732657,0},
    {128,270201093290129833730702342604831702973,1}};
  cases=Table[Module[{n=s[[1]],prefix=s[[2]],a=s[[3]],short,long,ss,ll,cone,cells=0,ok=True},
    short=prefix+2^n*(a+2);long=prefix+2^n*(a+2*(1-a)+4);
    ss=NestList[q,short,h];ll=NestList[q,long,h];
    Do[Module[{w=IntegerLength[row,2],initial,ca,it},
      initial=Join[ConstantArray[0,h+1],Reverse[IntegerDigits[row,2]],ConstantArray[0,3*h+1]];
      ca=CellularAutomaton[30,initial,h];it=NestList[q,row,h];
      cells+= (h+1)*w;
      ok=ok&&And@@Flatten@Table[
        ca[[t+1,h+2+k+t]]==BitAnd[BitShiftRight[it[[t+1]],k],1],
        {t,0,h},{k,0,w-1}]
    ],{row,{short,long}}];
    <|"PrefixLength"->n,"BuiltinConesMatch"->ok,"ScalarCellsCompared"->cells,
      "FullStateReturnTimesAgree"->(((#==short)& /@ ss)===((#==long)& /@ ll)),
      "OrbitEqualityRelationsAgree"->And@@Flatten@Table[
        (ss[[i]]==ss[[j]])===(ll[[i]]==ll[[j]]),{i,h+1},{j,h+1}]|>
  ],{s,samples}];
  <|"FiniteControlsOnly"->True,"LeanVerifiedByThisCalculation"->False,"FullProblemClaim"->False,
    "Cases"->cases,"BuiltinRule30Cones"->2*Length[cases],
    "ScalarCellsCompared"->Total[Lookup[cases,"ScalarCellsCompared"]],
    "AllPassed"->And@@Flatten[Lookup[cases,
      {"BuiltinConesMatch","FullStateReturnTimesAgree","OrbitEqualityRelationsAgree"}]]|>
];
