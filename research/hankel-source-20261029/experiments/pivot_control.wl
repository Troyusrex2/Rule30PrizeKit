rows = CellularAutomaton[30, {{1}, 0}, 4];
c = rows[[All, 5]];
h[n_] := Table[c[[i+j-1]], {i,n}, {j,n}];
f[a_,b_,d_] := BitXor[a,BitOr[b,d]];
evenOK = And@@Flatten[Table[
  f[BitXor[l,a],a,BitXor[a,b]] == BitXor[l,BitAnd[1-a,b]],
  {l,0,1},{a,0,1},{b,0,1}]];
oddOK = And@@Flatten[Table[f[a,BitXor[a,b],b] == BitAnd[1-a,b],{a,0,1},{b,0,1}]];
result = <|"centerPrefix"->c,"H2Rank"->MatrixRank[h[2],Modulus->2],
  "H3Rank"->MatrixRank[h[3],Modulus->2],"freshSource"->Times@@rows[[4,{5,6}]],
  "olderSource"->Times@@rows[[2,{4,5}]],"schurPivot"->Mod[c[[4]]+c[[5]],2],
  "even210Identity"->evenOK,"oddDefectIdentity"->oddOK|>;
Print[ExportString[result,"RawJSON"]];
