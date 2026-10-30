$HistoryLength=0;
fig=ArrayPlot[CellularAutomaton[30,{{1},0},40],Frame->True,
 ImageSize->520,PlotLabel->"Rule 30 from one black cell"];
control=Module[{},
mm[x_,y_]:=Mod[x.y,2];
mi[x_]:=Mod[Inverse[x],2];
gl2=Select[Partition[#,2]& /@ Tuples[{0,1},4],Mod[Det[#],2]==1&];
gv[v_]:=gl2[[1+FromDigits[v,2]]];
aa=bb={{0,1},{1,0}};
im[v_]:=Table[BitXor[v[[i]],BitOr[v[[i+1]],v[[i+2]]]],{i,Length[v]-2}];
mid[v_]:=Most[Rest[v]];
ell[v_]:=mm[mm[mi[gv[Rest[v]]],aa],gv[Most[v]]];
emm[v_]:=mm[mm[mi[gv[im[v]]],bb],gv[mid[v]]];
localCheck=And@@Table[mm[ell[im[v]],emm[Most[v]]]==mm[emm[Rest[v]],ell[mid[v]]],{v,Tuples[{0,1},5]}];
ring={1,1,0,1,0};
windows=Table[Table[ring[[Mod[j+k-2,Length[ring]]+1]],{k,3}],{j,Length[ring]}];
prod=Fold[mm[#2,#1]&,IdentityMatrix[2],ell /@ windows];
h=gv[Take[ring,2]];
expected=mm[mm[mi[h],Mod[MatrixPower[aa,Length[ring]],2]],h];
<|"GroupOrder"->Length[gl2],"AmbientGroupIsNoncommutative"->
 AnyTrue[Tuples[gl2,2],mm[#[[1]],#[[2]]]!=mm[#[[2]],#[[1]]]&],
 "All32LocalEquations"->localCheck,"CyclicConjugacy"->(prod==expected),
 "Product"->prod,"Expected"->expected|>
];

If[!TrueQ[control["All32LocalEquations"]]||!TrueQ[control["CyclicConjugacy"]]||
 !TrueQ[control["AmbientGroupIsNoncommutative"]]||control["GroupOrder"]=!=6,
 Print["matrix_control_failed"];Exit[1]];
Export["D:/MWB/Rule30/agent-coordination/block-20261030T004443Z/essay/wolfram-matrix-control.json",control,"RawJSON"];
Export["D:/MWB/Rule30/agent-coordination/block-20261030T004443Z/essay/figure-seed.png",fig,"PNG"];
Print["independent_GL2_positive_control_passed"];
