root = DirectoryName[$InputFileName];
cases = Import[FileNameJoin[{root,"control-cases.json"}],"RawJSON"];
steps = 32; checked = 0; results = {};
Do[
  m = c["width"]; q = c["state"];
  aa = If[TrueQ[Lookup[c,"check_extension",False]],c["extended_a"],c["initial_a"]];
  bb = If[TrueQ[Lookup[c,"check_extension",False]],c["extended_b"],c["initial_b"]];
  w = If[TrueQ[Lookup[c,"check_extension",False]],m+1,m];
  lo = -w; hi = 2 (steps+2)+1;
  init[z_] := Table[If[-w < p <= 0,BitGet[z,-p],0],{p,lo,hi}];
  ca = CellularAutomaton[30,init[aa],steps+2];
  cb = CellularAutomaton[30,init[bb],steps+2];
  av[t_,j_] := ca[[t+1,t-j-lo+1]];
  bv[t_,j_] := cb[[t+1,t-j-lo+1]];
  ok = If[q==16,
    And @@ Flatten[Table[{av[t+1,m-1]==1-av[t,m-1],
      BitXor[av[t+2,m-2],bv[t+2,m-2]]==BitXor[av[t,m-2],bv[t,m-2]]},{t,0,steps}]],
    And @@ Table[BitOr[av[t,m-1],av[t,m-2]]==BitOr[bv[t,m-1],bv[t,m-2]],{t,0,steps}]];
  If[TrueQ[Lookup[c,"check_extension",False]],
    ok = ok && AnyTrue[Range[0,steps],(av[#,m]==bv[#,m])&]];
  checked += 2 (steps+3) w;
  AppendTo[results,<|"state"->q,"width"->m,"passed"->ok|>],{c,cases}];
result = <|"passed"->And @@ Lookup[results,"passed"],"cases"->results,
  "built_in_cellular_automaton"->30,"scalar_cells_available"->checked,
  "causal_cone_stays_inside_initial_array"->True,"WolframVersionNumber"->$VersionNumber,
  "Lean_verified"->False,"Wolfram_backend_verification"->False,"full_problem_solved"->False|>;
Export[FileNameJoin[{root,"wolfram-control.json"}],result,"RawJSON"];
Print[ExportString[result,"RawJSON"]];
Exit[If[TrueQ[result["passed"]],0,1]];
