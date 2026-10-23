
Clear[check];
check[k_Integer,n_Integer,w_String] := Module[{a,rows,right,clauses,formula,result},
 a=Join[ConstantArray[False,n],Characters[w]/.{"0"->False,"1"->True}];
 rows=Table[Unique["s"],{Length[a]+1},{k}];
 right=Table[Unique["b"],{Length[a]}];
 clauses=Flatten[Table[
   Equivalent[rows[[t+1,j]],
     Xor[If[j==1,a[[t]],rows[[t,j-1]]],
       Or[rows[[t,j]],If[j==k,right[[t]],rows[[t,j+1]]]]]],
   {t,Length[a]},{j,k}]];
 formula=And@@Join[clauses,Not/@Last[rows]];
 result=TimeConstrained[SatisfiableQ[formula],25,"timeout"];
 <|"word"->w,"width"->k,"whiteSteps"->n,"vacuumReachable"->result|>
];
{$Version,check[7,4,"100101"]}
