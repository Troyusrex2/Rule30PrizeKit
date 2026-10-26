pattern = CellularAutomaton[30, {{1}, 0}, 32];
ImageResize[Image[1-pattern, "Bit"], 500, Resampling -> "Nearest"]
centerPrefix=pattern[[All,Ceiling[Length[First[pattern]]/2]]];
StringJoin[ToString/@centerPrefix]
halfStep[a_Integer]:=BitXor[a,BitOr[BitShiftRight[a,1],BitShiftRight[a,2]]];
gaugeStep[a_Integer,h_Integer]:=BitXor[h,BitShiftRight[h,1],
 BitAnd[BitNot[BitShiftRight[a,1]],BitShiftRight[h,2]]];
wedgeMask[a_Integer,h_Integer]:=BitXor[BitAnd[BitShiftRight[a,1],h],
 BitAnd[a,BitShiftRight[h,1]]];
a0=5;h0=1;a1=halfStep[a0];h1=gaugeStep[a0,h0];
finiteGapControl={wedgeMask[a0,h0],wedgeMask[a1,h1]};
resetPrefix=Table[pattern[[17,Ceiling[Length[First[pattern]]/2]+16-j]],{j,0,4}];
{finiteGapControl,resetPrefix}
If[finiteGapControl=!={0,1}||resetPrefix=!={1,0,0,0,0}||
 !StringStartsQ[StringJoin[ToString/@centerPrefix],"1101110011000101"],
 Print["Exploration control failed"];Exit[2]];
record=<|"pass"->True,"finiteGapControl"->finiteGapControl,"resetPrefix"->resetPrefix,
 "centerPrefixControl"->True,"proofCellsExecuted"->False,"freshNotebookVerified"->False|>;
Export["D:/MWB/Rule30/wolfram-local/agent-seven-20261024/band-mechanism-20261026T0004/essay-combined/exploration-controls.json",record,"RawJSON"];
Print[ExportString[record,"RawJSON"]];Exit[0];
