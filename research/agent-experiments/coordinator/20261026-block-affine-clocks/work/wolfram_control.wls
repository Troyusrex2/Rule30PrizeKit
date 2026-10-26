root=DirectoryName[$InputFileName]; cases=0; comparisons=0; ok=True;
Do[
  P=2^Quotient[2 m-1,3];lo=-m;hi=4 P+1;
  Do[
    init=Table[If[-m<p<=0,BitGet[z,-p],0],{p,lo,hi}];
    ca=CellularAutomaton[30,init,2 P];
    pass=And@@Flatten[Table[
      ca[[t+P+1,t+P-j-lo+1]]==ca[[t+1,t-j-lo+1]],{t,0,P},{j,0,m-1}]];
    ok=ok&&pass;cases++;comparisons+=(P+1) m,
    {z,0,2^m-1}],{m,1,8}];
result=<|"passed"->ok,"initial_rows"->cases,"maximum_width"->8,
 "period_cell_comparisons"->comparisons,"built_in_cellular_automaton"->30,
 "causal_cone_stays_inside_initial_array"->True,"WolframVersionNumber"->$VersionNumber,
 "Lean_verified"->False,"Wolfram_backend_verification"->False,"full_problem_solved"->False|>;
Export[FileNameJoin[{root,"wolfram-control.json"}],result,"RawJSON"];
Print[ExportString[result,"RawJSON"]];Exit[If[TrueQ[ok],0,1]];
