(* Independent physical controls; no cloud sign-in or submission calls. *)
SeedRandom[302413];
width = 24;
Clear[history];
history[a_List] := Module[{r, row, hist},
  r[m_, t_] := If[m == 0, 0, If[m == 1, a[[t + 1]],
    r[m, t] = BitXor[r[m - 1, t + 1], BitOr[r[m - 1, t], r[m - 2, t]]]]];
  row = Append[Reverse[Table[r[m, 0], {m, 1, width}]], 0];
  hist = NestList[
    Function[v, ReplacePart[Last[CellularAutomaton[30, v, 1]], -1 -> 0]],
    row, width - 1];
  If[Table[hist[[t + 1, width]], {t, 0, width - 1}] =!= Take[a, width],
    Print["Physical head realization control failed"]; Exit[1]];
  hist
];
checks = zero = nonzero = headChecks = 0;
Do[
  a = RandomInteger[{0, 1}, width + 2]; base = history[a];
  headChecks += width;
  Do[
    b = ReplacePart[a, t + k + 1 -> 1 - a[[t + k + 1]]];
    changed = history[b]; headChecks += width;
    lhs = BitXor[base[[t + 1, width - (k + 2) + 1]],
      changed[[t + 1, width - (k + 2) + 1]]];
    rhs = Mod[Boole[EvenQ[k]] + Total[
      Table[base[[t + k - j + 1, width - j + 1]], {j, 1, k}]], 2];
    If[lhs =!= rhs, Print["One-entry-behind sensitivity control failed"]; Exit[1]];
    checks++; If[rhs == 0, zero++, nonzero++],
    {k, 0, 12}, {t, 0, 3}],
  {example, 1, 16}];
report = <|"all_passed" -> True,
  "physical_penultimate_flip_checks" -> checks,
  "physical_head_realization_checks" -> headChecks,
  "zero_sensitivity_cases" -> zero, "unit_sensitivity_cases" -> nonzero,
  "independent_builtin" -> "CellularAutomaton[30]",
  "spatial_width" -> width, "only_uncontaminated_causal_cones_compared" -> True,
  "WolframVersion" -> $Version,
  "Lean_verified_by_this_script" -> False,
  "Q01_proved" -> False, "full_problem_solved" -> False|>;
Export[FileNameJoin[{DirectoryName[$InputFileName], "odd-sensitivity-controls.json"}], report, "RawJSON"];
Print[ExportString[report, "RawJSON", "Compact" -> True]];
Exit[0];
