ClearAll[at, bit, first, second];
steps = 64; interior = 32; width = 2 steps + interior;
pa = {168,212,172,178,202,43,172,178};
pb = {168,180,204,170,170,117,138,77};
tail = {202,43,172,178};
at[p_, k_] := If[k < 8, p[[k+1]], tail[[Mod[k-8,4]+1]]];
bit[p_, t_, k_] := Mod[Quotient[at[p,k],2^Mod[t,8]],2];
first[k_] := Boole[k >= 5 && Mod[k,4] == 1];
second[k_] := Boole[(k >= 5 && Mod[k,4] == 1) || k == 7];
a = CellularAutomaton[30,Table[first[k],{k,0,width-1}],steps];
b = CellularAutomaton[30,Table[second[k],{k,0,width-1}],steps];
ok = And @@ Flatten[Table[
  {a[[t+1,t+k+1]] == bit[pa,t,k], b[[t+1,t+k+1]] == bit[pb,t,k]},
  {t,0,steps},{k,0,interior-1}]];
result = <|"passed"->ok,"built_in_cellular_automaton"->30,
  "scalar_cells_checked"->2 (steps+1) interior,"time_steps"->steps,
  "causal_cone_stays_inside_initial_array"->True,
  "WolframVersionNumber"->$VersionNumber,"Lean_verified"->False,
  "full_problem_solved"->False|>;
Export[FileNameJoin[{DirectoryName[$InputFileName],"wolfram-control.json"}],result,"RawJSON"];
Print[ExportString[result,"RawJSON"]];
Exit[If[TrueQ[ok],0,1]];
