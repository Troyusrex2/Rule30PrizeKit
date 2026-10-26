root=DirectoryName[$InputFileName];rows=0;cases=0;checks=0;flags={0,0};ok=True;
Do[Do[rows++;
 Do[
  P=2^Quotient[2 j+3,3];lo=-m-2;hi=8 P+4;
  init=Table[If[-m<p<=0,BitGet[z,-p],0],{p,lo,hi}];
  ca=CellularAutomaton[30,init,4 P+1];
  profiles=Table[Table[ca[[t+1,t-d-lo+1]],{t,0,4 P+1}],{d,j,j+3}];
  {l,k,h,g}=profiles;
  ok=ok && And@@Table[k[[t+P+1]]==k[[t+1]],{t,0,2 P}];
  If[And@@Table[h[[t+P+1]]==1-h[[t+1]],{t,0,2 P}],
   cases++;q=Table[BitXor[g[[t+P+1]],g[[t+1]]],{t,0,3 P}];
   rr=MapThread[BitOr,{g,h}];rho=Table[BitXor[rr[[t+P+1]],rr[[t+1]]],{t,0,3 P}];
   e=BitXor[q[[P+1]],q[[1]]];flags[[e+1]]++;
   pass=And@@Table[
     q[[t+2]]==BitXor[q[[t+1]],1-k[[t+1]]] &&
     rho[[t+1]]==BitXor[1-g[[t+1]],h[[t+1]] q[[t+1]]] &&
     BitXor[rho[[t+2]],rho[[t+1]]]==(1-q[[t+1]]) BitXor[h[[t+2]],h[[t+1]]] &&
     q[[t+P+1]]==BitXor[q[[t+1]],e] &&
     g[[t+2 P+1]]==BitXor[g[[t+1]],e],{t,0,P}];
   ok=ok&&pass;checks+=5(P+1)],
 {j,0,m-4}],{z,0,2^m-1}],{m,1,9}];
result=<|"passed"->ok,"initial_rows"->rows,"antiperiodic_cases"->cases,
 "plateau_flag_cases"->flags[[1]],"double_flag_cases"->flags[[2]],
 "identity_comparisons"->checks,"maximum_width"->9,
 "built_in_cellular_automaton"->30,"WolframVersionNumber"->$VersionNumber,
 "Wolfram_backend_verification"->False,"Lean_verified"->False,"full_problem_solved"->False|>;
Export[FileNameJoin[{root,"wolfram-control.json"}],result,"RawJSON"];
Print[ExportString[result,"RawJSON"]];Exit[If[TrueQ[ok],0,1]];
