Needs["Wolfram`LeanLink`"];
root=DirectoryName[$InputFileName];dir=FileNameJoin[{root,"essay"}];
$CloudConnected;
converter=ResourceFunction["https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Function/MarkdownToNotebook"];
converter[FileNameJoin[{dir,"essay.md"}],FileNameJoin[{dir,"product-parity-preview-unevaluated.nb"}],
 "Evaluate"->False,"UseCache"->False,"EvaluateSeparator"->None];
nb=Import[FileNameJoin[{dir,"product-parity-preview-unevaluated.nb"}],"NB"];
inputs=Cases[nb,Cell[BoxData[b_],"Input",___]:>b,Infinity];
iconized=!FreeQ[nb,"IconizedObject"];
held=ToExpression[#,StandardForm,HoldComplete]&/@inputs;
embedded=Cases[held,HoldPattern[LeanImportString[s_String,___]]:>s,Infinity];
If[Length[inputs]=!=7||!TrueQ[iconized]||Length[embedded]=!=1,
 Print[{"Preview packaging failed",Length[inputs],iconized,Length[embedded]}];Exit[2]];
stream=OpenWrite[FileNameJoin[{dir,"preview-extracted.lean"}],BinaryFormat->True];
BinaryWrite[stream,ToCharacterCode[First[embedded],"UTF-8"],"Byte"];Close[stream];
sha=FileHash[FileNameJoin[{dir,"preview-extracted.lean"}],"SHA256","HexString"];
If[sha=!=FileHash[FileNameJoin[{dir,"Rule30Submission.lean"}],"SHA256","HexString"],
 Print["Preview source differs"];Exit[3]];
record=<|"packagingPass"->True,"sourceIconized"->True,"sourceRoundTrip"->True,
 "sourceSHA256"->sha,"inputCells"->7,"Evaluate"->False,"UseCache"->False,
 "proofCellsExecuted"->False,"freshNotebookVerified"->False,"submitted"->False,
 "notebookSHA256"->FileHash[FileNameJoin[{dir,"product-parity-preview-unevaluated.nb"}],"SHA256","HexString"]|>;
Export[FileNameJoin[{dir,"preview-packaging.json"}],record,"RawJSON"];
Print[ExportString[record,"RawJSON"]];Exit[0];
