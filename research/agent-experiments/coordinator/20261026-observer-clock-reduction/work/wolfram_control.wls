root=DirectoryName[$InputFileName];cases=0;pairs=0;anti=0;withzero=0;checks=0;ok=True;
Do[Do[
 cases++;
 Do[
  P=2^Quotient[2 j-1,3];lo=-m-2;hi=4 P+2;
  init=Table[If[-m<p<=0,BitGet[z,-p],0],{p,lo,hi}];
  ca=CellularAutomaton[30,init,2 P];
  g=Table[ca[[t+1,t-j-lo+1]],{t,0,2 P}];
  h=Table[ca[[t+1,t-j+1-lo+1]],{t,0,2 P}];
  k=Table[ca[[t+1,t-j+2-lo+1]],{t,0,2 P}];
  ok=ok && And@@Table[h[[t+P+1]]==h[[t+1]] && k[[t+P+1]]==k[[t+1]],{t,0,P}];
  pairs++;
  If[And@@Table[g[[t+P+1]]==1-g[[t+1]],{t,0,P}],
    anti++;If[MemberQ[h,0],withzero++];
    ok=ok && And@@Table[BitXor[BitOr[g[[t+1]],h[[t+1]]],BitOr[g[[t+P+1]],h[[t+P+1]]]]==1-h[[t+1]],{t,0,P}];
    checks+=P+1],
 {j,2,m-1}],{z,0,2^m-1}],{m,1,8}];
result=<|"passed"->ok,"initial_rows"->cases,"profile_pairs"->pairs,
 "antiperiodic_cases"->anti,"antiperiodic_with_mask_zero"->withzero,
 "mask_recovery_comparisons"->checks,"maximum_width"->8,
 "built_in_cellular_automaton"->30,"WolframVersionNumber"->$VersionNumber,
 "Wolfram_backend_verification"->False,"Lean_verified"->False,"full_problem_solved"->False|>;
Export[FileNameJoin[{root,"wolfram-control.json"}],result,"RawJSON"];
Print[ExportString[result,"RawJSON"]];Exit[If[TrueQ[ok],0,1]];
