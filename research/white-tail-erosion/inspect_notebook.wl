(* Inspect the saved artifact without reevaluating its proof or input cells. *)
ClearAll[inspectWhiteTailNotebook];
inspectWhiteTailNotebook[notebookFile_String, sourceFile_String] := Module[
  {notebook,inputs,held,sources,expected,outputs,messages,controlBoxes,control,
   graphics,figures,outputText,report},
  Needs["Wolfram`LeanLink`"];
  notebook=Get[notebookFile,CharacterEncoding->"UTF-8"];
  expected="import Rule30PrizeKit\n"<>FromCharacterCode[BinaryReadList[sourceFile],"UTF-8"];
  inputs=Cases[notebook,Cell[BoxData[b_],"Input",___]:>b,Infinity];
  held=ToExpression[#,StandardForm,HoldComplete]& /@ inputs;
  sources=Cases[held,HoldPattern[LeanImportString[s_String,___]]:>s,Infinity];
  If[sources=!={expected},Return[Failure["SavedSourceMismatch",<|"SourceCount"->Length[sources]|>]]];
  outputs=Cases[notebook,Cell[BoxData[b_],"Output",___]:>b,Infinity];
  messages=Cases[notebook,Cell[b_,"Message",___]:>HoldComplete[b],Infinity];
  outputText=ToString[outputs,InputForm];
  If[!StringContainsQ[outputText,"KernelChecked"],Return[Failure["MissingKernelOutput",<||>]]];
  controlBoxes=Select[outputs,StringContainsQ[ToString[#,InputForm],
    "BuiltinConeMatchesDrivenHalfUntilDeparture"]&];
  If[Length[controlBoxes]=!=1,Return[Failure["ControlOutputCount",<|"Count"->Length[controlBoxes]|>]]];
  control=ToExpression[First[controlBoxes],StandardForm];
  If[!AssociationQ[control]||!TrueQ[control["AllPassed"]]||
     control["BuiltinRule30Cones"]=!=12||control["ScalarCellsCompared"]=!=5810,
    Return[Failure["SavedControlOutput",<|"Head"->Head[control]|>]]];
  (* LeanLink's environment output has decorative graphics too. Select the
     two data figures by their saved labels, rather than counting its icons. *)
  graphics=Cases[outputs,g_GraphicsBox /; StringContainsQ[ToString[g,InputForm],
    "Rule 30 from a single black cell"|"Black marks a defect from the ether"]:>g,Infinity];
  If[Length[graphics]=!=2,Return[Failure["FigureCount",<|"Count"->Length[graphics]|>]]];
  figures=MapThread[Function[{boxes,name},TimeConstrained[
    Export[FileNameJoin[{DirectoryName[notebookFile],name}],ToExpression[boxes,StandardForm],"PNG"],
    30,$Failed]],{graphics,{"figure-seed.png","figure-driven-difference.png"}}];
  report=<|"SavedNotebookSourceRoundTripPassed"->True,
    "SavedKernelCheckedOutputPresent"->True,"SavedIndependentControlsPassed"->True,
    "BuiltinRule30Cones"->control["BuiltinRule30Cones"],
    "ScalarCellsCompared"->control["ScalarCellsCompared"],
    "InputCells"->Length[inputs],"OutputCells"->Length[outputs],
    "MessageCells"->Length[messages],"GraphicsOutputs"->Length[graphics],
    "FigurePNGExportsSucceeded"->AllTrue[figures,StringQ[#]&&FileExistsQ[#]&],
    "NotebookSHA256"->IntegerString[FileHash[notebookFile,"SHA256"],16,64],
    "PrizeAPISubmitted"->False|>;
  Export[notebookFile<>".inspection.json",report,"RawJSON"];
  report
];
