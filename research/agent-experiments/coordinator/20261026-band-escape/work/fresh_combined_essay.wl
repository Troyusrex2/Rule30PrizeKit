Needs["Wolfram`LeanLink`"];
root=DirectoryName[$InputFileName];dir=FileNameJoin[{root,"essay-combined"}];
nb=Import[FileNameJoin[{dir,"common-gauge-essay.nb"}],"NB"];
inputs=Cases[nb,Cell[BoxData[b_],"Input",___]:>b,Infinity];
iconized=!FreeQ[nb,"IconizedObject"];
If[Length[inputs]=!=7||!TrueQ[iconized],Print["Notebook shape failed"];Exit[2]];
Do[Print["Fresh plain-kernel cell ",i];value=ToExpression[inputs[[i]],StandardForm];
 Print[Head[value]],{i,Length[inputs]}];
If[!MatchQ[rule30Submission,_LeanEnvironment]||!MatchQ[formalKernelCheck,_Success],
 Print["Fresh environment or kernel check failed"];Exit[3]];
If[Lookup[formalKernelCheck[[2]],"Declarations",0]=!=164,Print["Wrong declaration count"];Exit[4]];
If[finiteGapControl=!={0,1}||resetPrefix=!={1,0,0,0,0}||
 !StringStartsQ[StringJoin[ToString/@centerPrefix],"1101110011000101"],
 Print["Physical exploration control failed"];Exit[5]];
held=ToExpression[#,StandardForm,HoldComplete]&/@inputs;
embedded=Cases[held,HoldPattern[LeanImportString[s_String,___]]:>s,Infinity];
If[Length[embedded]=!=1,Print["Expected one embedded source"];Exit[6]];
stream=OpenWrite[FileNameJoin[{dir,"notebook-extracted.lean"}],BinaryFormat->True];
BinaryWrite[stream,ToCharacterCode[First[embedded],"UTF-8"],"Byte"];Close[stream];
sha=FileHash[FileNameJoin[{dir,"notebook-extracted.lean"}],"SHA256","HexString"];
If[sha=!=FileHash[FileNameJoin[{dir,"Rule30Submission.lean"}],"SHA256","HexString"],
 Print["Source round-trip differs"];Exit[7]];
record=<|"freshKernelEvaluation"->True,"isLeanEnvironment"->True,"kernelCheckSuccess"->True,
 "replayedDeclarations"->164,"inputCells"->7,"sourceIconized"->True,"sourceRoundTrip"->True,
 "sourceSHA256"->sha,"notebookSHA256"->FileHash[FileNameJoin[{dir,"common-gauge-essay.nb"}],"SHA256","HexString"],
 "singleSeedPrefixControl"->True,"finiteGapControl"->True,"submitted"->False|>;
Export[FileNameJoin[{dir,"notebook-fresh-check.json"}],record,"RawJSON"];
Print[ExportString[record,"RawJSON"]];Exit[0];
