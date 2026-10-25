Needs["Wolfram`LeanLink`"];
root=DirectoryName[$InputFileName];dir=FileNameJoin[{root,"essay"}];
$CloudConnected;
md2nb=ResourceFunction["https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Function/MarkdownToNotebook"];
Print["Converting the seven-cell computational essay with fresh cell evaluation"];
result=md2nb[FileNameJoin[{dir,"essay.md"}],FileNameJoin[{dir,"product-parity-essay.nb"}],"UseCache"->False,"EvaluateSeparator"->None];
If[!FileExistsQ[FileNameJoin[{dir,"product-parity-essay.nb"}]],Print["Notebook missing"];Exit[2]];
nb=Import[FileNameJoin[{dir,"product-parity-essay.nb"}],"NB"];
inputs=Cases[nb,Cell[BoxData[b_],"Input",___]:>b,Infinity];
iconized=!FreeQ[nb,"IconizedObject"];
If[Length[inputs]=!=7||!TrueQ[iconized],Print[{"Notebook shape failed",Length[inputs],iconized}];Exit[3]];
(* Conversion restores caller assignments. Inspect its recorded outputs, then
   use a separate fresh process for the actual independent cell replay. *)
outputs=Cases[nb,Cell[BoxData[b_],"Output",___]:>ToExpression[b,StandardForm,HoldComplete],Infinity];
checks=Cases[outputs,Success["KernelChecked",a_Association]:>a,Infinity];
If[Length[checks]=!=1||Lookup[First[checks],"Declarations",0]=!=207,
 Print[{"No recorded complete kernel replay",checks}];Exit[4]];
record=<|"built"->True,"inputCells"->7,"sourceIconized"->True,"UseCache"->False,
 "recordedKernelReplayDeclarations"->207,"freshNotebookVerified"->False,
 "notebookSHA256"->FileHash[FileNameJoin[{dir,"product-parity-essay.nb"}],"SHA256","HexString"],
 "submitted"->False|>;
Export[FileNameJoin[{dir,"notebook-build.json"}],record,"RawJSON"];
Print[ExportString[record,"RawJSON"]];Exit[0];
