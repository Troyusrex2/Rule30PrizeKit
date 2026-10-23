ClearAll[columnFrontReport];
columnFrontReport[] := Module[{grid,left,right,lags,residues},
  grid=CellularAutomaton[30,{{1},0},{530,{-530,530}}];
  left[t_]:=Sum[grid[[t+1,531-t+j]] 2^j,{j,0,19}];
  right[t_]:=Sum[grid[[t+1,531+t-j]] 2^j,{j,0,19}];
  lags=Table[FirstPosition[Table[
    Unequal[grid[[m+j+1,531-m]],grid[[m+j+1,531+m]]],{j,0,18}],True,
    Missing["NoWitness"]],{m,1,512}];
  residues=Table[AnyTrue[Range[0,18],Function[j,
    BitGet[left[20+Mod[r+j,4]],j]!=BitGet[right[Mod[r+j,256]],j]]],{r,0,255}];
  <|"engineVersion"->$VersionNumber,"finiteCrosschecksOnly"->True,
    "gridDimensions"->Dimensions[grid],"frontWidth"->20,
    "rightCycleCloses"->SameQ[right[256],right[0]],
    "leftCycleCloses"->SameQ[left[24],left[20]],
    "leftCycle"->Table[left[t],{t,20,23}],
    "all256ResiduesSeparated"->And@@residues,
    "all512SampleMirrorPairsSeparated"->FreeQ[lags,_Missing],
    "exampleM256Lag"->First[lags[[256]]]-1|>
];
