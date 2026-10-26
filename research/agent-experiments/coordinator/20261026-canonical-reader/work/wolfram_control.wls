root=DirectoryName[$InputFileName];cases=0;cells=0;ok=True;
canonical[xs_]:=Module[{p=FirstPosition[xs,1],n=Length[xs]},
  If[MissingQ[p],True,With[{i=First[p]},i>=n-1 || (i+3<=n && xs[[i+1]]==xs[[i+2]])]]];
Do[Do[
  xs=Table[BitGet[z,j],{j,0,m-1}];lo=-m-2;hi=4;
  init=Table[If[-m<p<=0,xs[[1-p]],0],{p,lo,hi}];
  ca=CellularAutomaton[30,init,1];
  ys=Table[ca[[2,1-j-lo+1]],{j,0,m-1}];
  ok=ok && canonical[xs]==canonical[ys];cases++;cells+=m,
  {z,0,2^m-1}],{m,1,10}];
result=<|"passed"->ok,"initial_rows"->cases,"literal_builtin_cells"->cells,
 "maximum_width"->10,"built_in_cellular_automaton"->30,
 "WolframVersionNumber"->$VersionNumber,"Wolfram_backend_verification"->False,
 "Lean_verified"->False,"full_problem_solved"->False|>;
Export[FileNameJoin[{root,"wolfram-control.json"}],result,"RawJSON"];
Print[ExportString[result,"RawJSON"]];Exit[If[TrueQ[ok],0,1]];
