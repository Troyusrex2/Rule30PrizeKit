Get[FileNameJoin[{DirectoryName[$InputFileName], "spacing-probe.wl"}]];
ClearAll[spacingGapReport];
spacingGapReport[] := Module[{g, columns, whites},
  g = Function[r, MemberQ[{0,3,6,9,12,15,18,21,26}, Mod[r,31]]];
  columns = spacingColumns[g, 544, 1];
  whites = Table[columns[[d+1,1]], {d,528,544}];
  <|"FiniteExperimentOnly" -> True, "GatePeriod" -> 31,
    "WhiteDepths" -> Range[528,544], "ObservedCells" -> whites,
    "AllSeventeenWhite" -> And @@ (Not /@ whites),
    "GapConstraintCheckedAcrossTwoPeriods" -> And @@ Table[
      If[g[r], (!g[r+1] && !g[r+2] &&
        (g[r+3] || (!g[r+3] && !g[r+4] && g[r+5]))), True], {r,0,61}],
    "FiniteRightRealizabilityClaim" -> False, "FullProblemClaim" -> False|>
];
