root=DirectoryName[$InputFileName];
nb=Get[FileNameJoin[{root,"delayed-defect-essay.nb"}],CharacterEncoding->"UTF-8"];
If[Head[nb]=!=Notebook,Print["Notebook parse failed"];Exit[2]];
inputs=Cases[nb,Cell[BoxData[b_],"Input",___]:>b,Infinity];
Print["Fresh kernel: evaluating ",Length[inputs]," input cells"];
Do[Print["Cell ",i];result=ToExpression[inputs[[i]],StandardForm];
 Print[{"result head",Head[result],"environment head",Head[rule30Submission]}],{i,Length[inputs]}];
If[!MatchQ[rule30Submission,_LeanEnvironment]||!MatchQ[formalKernelCheck,_Success],
 Print[{"Fresh evaluation did not produce a kernel-checked environment",Head[rule30Submission],Head[formalKernelCheck]}];Exit[3]];
If[!StringStartsQ[StringJoin[ToString/@centerPrefix],"1101110011000101"],
 Print["Single-seed center control differs"];Exit[6]];
Export[FileNameJoin[{root,"essay-preview-data.json"}],preview,"RawJSON"];
held=ToExpression[#,StandardForm,HoldComplete]&/@inputs;
embedded=Cases[held,HoldPattern[LeanImportString[s_String,___]]:>s,Infinity];
If[Length[embedded]!=1,Print["Expected exactly one embedded source"];Exit[4]];
stream=OpenWrite[FileNameJoin[{root,"notebook-extracted.lean"}],BinaryFormat->True];
BinaryWrite[stream,ToCharacterCode[First[embedded],"UTF-8"],"Byte"];Close[stream];
sourceHash=FileHash[FileNameJoin[{root,"notebook-extracted.lean"}],"SHA256","HexString"];
expected=FileHash[FileNameJoin[{root,"Rule30Submission.lean"}],"SHA256","HexString"];
If[sourceHash=!=expected,Print["Extracted source differs"];Exit[5]];
record=<|"freshKernelEvaluation"->True,"isLeanEnvironment"->True,
 "kernelCheckSuccess"->True,"inputCells"->Length[inputs],"sourceSHA256"->sourceHash,
 "notebookSHA256"->FileHash[FileNameJoin[{root,"delayed-defect-essay.nb"}],"SHA256","HexString"],
 "sourceRoundTrip"->True,"singleSeedPrefixControl"->True,"submitted"->False|>;
Export[FileNameJoin[{root,"essay-fresh-check.json"}],record,"RawJSON"];
Print[ExportString[record,"RawJSON"]];
Exit[0];
