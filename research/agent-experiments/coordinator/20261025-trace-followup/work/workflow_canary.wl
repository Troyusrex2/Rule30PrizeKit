Needs["Wolfram`LeanLink`"];
root=DirectoryName[$InputFileName];dir=FileNameJoin[{root,"essay"}];
If[stage==="build",
 $CloudConnected;
 converter=ResourceFunction["https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Function/MarkdownToNotebook"];
 converter[FileNameJoin[{dir,"workflow-canary.md"}],FileNameJoin[{dir,"workflow-canary.nb"}],"UseCache"->False,"EvaluateSeparator"->None];
];
nb=Import[FileNameJoin[{dir,"workflow-canary.nb"}],"NB"];
inputs=Cases[nb,Cell[BoxData[b_],"Input",___]:>b,Infinity];
iconized=!FreeQ[nb,"IconizedObject"];
If[Length[inputs]=!=3||!TrueQ[iconized],Print["Canary shape failed"];Exit[2]];
If[stage==="build",
 outputs=Cases[nb,Cell[BoxData[b_],"Output",___]:>ToExpression[b,StandardForm,HoldComplete],Infinity];
 checks=Cases[outputs,Success["KernelChecked",a_Association]:>a,Infinity];
 If[Length[checks]=!=1||Lookup[First[checks],"Declarations",0]=!=1,
  Print[{"Canary stored check missing",checks,outputs}];Exit[3]],
 Do[ToExpression[b,StandardForm],{b,inputs}];
 If[!MatchQ[canaryEnvironment,_LeanEnvironment]||!MatchQ[canaryKernelCheck,_Success]||
   Lookup[canaryKernelCheck[[2]],"Declarations",0]=!=1,
   Print["Canary fresh environment or replay failed"];Exit[4]];
 held=ToExpression[#,StandardForm,HoldComplete]&/@inputs;
 embedded=Cases[held,HoldPattern[LeanImportString[s_String,___]]:>s,Infinity];
 expected=FromCharacterCode[BinaryReadList[FileNameJoin[{dir,"workflow-canary-source.lean"}]],"UTF-8"];
 If[embedded=!={expected},Print["Canary embedded source differs"];Exit[5]];
];
record=<|"pass"->True,"stage"->stage,"sourceIconized"->True,"inputCells"->3,
 "completeKernelReplayDeclarations"->1,"separateFreshProcess"->(stage==="fresh"),
 "sourceRoundTrip"->(stage==="fresh"),"prizeNotebookValidated"->False,"submitted"->False,
 "notebookSHA256"->FileHash[FileNameJoin[{dir,"workflow-canary.nb"}],"SHA256","HexString"]|>;
Export[FileNameJoin[{dir,"workflow-canary-"<>stage<>".json"}],record,"RawJSON"];
Print[ExportString[record,"RawJSON"]];Exit[0];
