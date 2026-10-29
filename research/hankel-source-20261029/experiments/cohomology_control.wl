image[w_,k_] := Sum[BitXor[BitGet[w,j],BitOr[BitGet[w,j+1],BitGet[w,j+2]]]*2^j,{j,0,k-1}];
records=Table[
 nr=2^k;nj=2 nr;
 mat=Table[
  old=BitAnd[BitShiftRight[w,1],nr-1];new=image[w,k];
  jl=BitAnd[w,nj-1];jr=BitAnd[BitShiftRight[w,1],nj-1];
  Table[Mod[Boole[c==old]+Boole[c==new]+Boole[c==nr+jl]+Boole[c==nr+jr],2],{c,0,nr+nj-1}],
 {w,0,2^(k+2)-1}];
 fr=MatrixRank[mat,Modulus->2];jrk=MatrixRank[mat[[All,nr+1;;nr+nj]],Modulus->2];
 <|"width"->k,"constraintRank"->fr,"fluxRank"->jrk,"densityDimension"->nr-fr+jrk,"trivialDimension"->2^(k-1)|>,
 {k,1,6}];
Print[ExportString[records,"RawJSON"]];
