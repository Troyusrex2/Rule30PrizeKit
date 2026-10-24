(* Finite controls, independent of the unbounded Lean proof. *)
ClearAll[clockMaskReport];
clockMaskReport[] := Module[{q, orbit, cases={}, caChecks={}, row, p, h, profiles,
    aa, bb, cc, dd, ss, prev, w, horizon=32, initial, ca, iter, samples},
  q[x_] := BitXor[x, BitOr[BitShiftRight[x,1],BitShiftRight[x,2]]];
  Do[
    orbit={a}; row=q[a];
    While[row!=a, AppendTo[orbit,row]; row=q[row]];
    p=Length[orbit];
    If[p>=4,
      h=p/2; w=IntegerLength[a,2];
      profiles=Table[BitAnd[BitShiftRight[orbit,k],1],{k,0,w+3}];
      Do[
        {aa,bb,cc,dd}=profiles[[k+{1,2,3,4}]];
        If[RotateLeft[bb,h]===1-bb && RotateLeft[cc,h]===cc && RotateLeft[dd,h]===dd,
          ss=MapThread[BitOr,{aa,bb}];
          prev=If[k==0,True,RotateLeft[profiles[[k]],h]=!=profiles[[k]]];
          AppendTo[cases, <|"Word"->a,"Column"->k,"Clock"->p,
            "ORNonconstant"->(Length[DeleteDuplicates[ss]]==2),
            "ORNotHalfPeriodic"->(RotateLeft[ss,h]=!=ss),
            "PredecessorNotHalfPeriodicWhenPresent"->prev|>]
        ],{k,0,w-1}]
    ],{a,0,511}];
  samples={4,7,8,16,32,33,64,160,528,529};
  Do[
    w=IntegerLength[a,2];
    initial=Join[ConstantArray[0,horizon+1],Table[BitAnd[BitShiftRight[a,k],1],{k,0,w-1}],
      ConstantArray[0,3*horizon+1]];
    ca=CellularAutomaton[30,initial,horizon]; iter=NestList[q,a,horizon];
    AppendTo[caChecks,And@@Flatten@Table[
      ca[[t+1,horizon+2+k+t]]==BitAnd[BitShiftRight[iter[[t+1]],k],1],
      {t,0,horizon},{k,0,w-1}]],{a,samples}];
  <|"FiniteControlsOnly"->True,"LeanVerifiedByThisCalculation"->False,
    "FullProblemClaim"->False,"InitialWordsChecked"->512,
    "OnsetCasesChecked"->Length[cases],"BuiltinRule30Cones"->Length[samples],
    "AllPassed"->(Length[cases]>0 && And@@caChecks &&
      And@@Flatten[Lookup[cases,{"ORNonconstant","ORNotHalfPeriodic",
        "PredecessorNotHalfPeriodicWhenPresent"}]]),"Cases"->cases|>
];
