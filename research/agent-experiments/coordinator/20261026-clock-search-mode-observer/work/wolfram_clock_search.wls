root=DirectoryName[$InputFileName];rows=0;cases=0;checks=0;ok=True;
scan[p_,0,rr_,s_]:=0;
scan[p_,n_,rr_,s_]:=If[rr[[s+1]]==rr[[s+p+1]],1-scan[p,n-1,rr,s+1],rr[[s+1]]];
Do[Do[rows++;
 Do[
  P=2^Quotient[2 j+3,3];lo=-m-2;hi=8 P+4;
  init=Table[If[-m<p<=0,BitGet[z,-p],0],{p,lo,hi}];
  ca=CellularAutomaton[30,init,4 P+1];
  profiles=Table[Table[ca[[t+1,t-d-lo+1]],{t,0,4 P+1}],{d,j,j+3}];
  {k,h,g,c}=profiles;
  If[And@@Table[h[[t+P+1]]==h[[t+1]] && g[[t+P+1]]==1-g[[t+1]],{t,0,2 P}] && MemberQ[Take[h,P],0],
   cases++;rr=MapThread[BitOr,{g,h}];dc=Table[BitXor[c[[t+2]],c[[t+1]]],{t,0,4 P}];
   ok=ok && dc==Take[rr,Length[dc]];
   Do[first=FirstPosition[Table[Boole[rr[[s+t+1]]!=rr[[s+t+P+1]]],{t,0,P-1}],1];
     If[MissingQ[first],ok=False;Break[]];u=first[[1]]-1;
     pred=BitXor[rr[[s+u+1]],Mod[u,2]];
     ok=ok && pred==g[[s+1]] && scan[P,u+1,rr,s]==g[[s+1]] && scan[P,P,rr,s]==g[[s+1]] && scan[P,P,dc,s]==g[[s+1]];
     checks+=4,{s,0,P-1}]],
 {j,0,m-3}],{z,0,2^m-1}],{m,1,9}];
result=<|"passed"->ok,"initial_rows"->rows,"anti_clock_cases_with_mask_zero"->cases,
 "phase_prediction_comparisons"->checks,"maximum_width"->9,
 "decoded_from_head_differences"->True,
 "built_in_cellular_automaton"->30,"WolframVersionNumber"->$VersionNumber,
 "Wolfram_backend_verification"->False,"full_problem_solved"->False|>;
Export[FileNameJoin[{root,"wolfram-clock-search.json"}],result,"RawJSON"];
Print[ExportString[result,"RawJSON"]];Exit[If[TrueQ[ok],0,1]];
