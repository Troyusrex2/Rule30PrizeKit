(* Evaluate and inspect a review notebook. This file never submits anything. *)
$CharacterEncoding = "UTF-8";
Needs["Wolfram`LeanLink`"];
renormDirectory = DirectoryName[$InputFileName];
renormConfig = Import[FileNameJoin[{renormDirectory,"notebook-config.json"}],"RawJSON"];
renormKit = Environment["RULE30PRIZE_KIT"];
If[!StringQ[renormKit] || !DirectoryQ[renormKit], Print[Failure["KitDirectory",<||>]]; Exit[1]];
$Rule30PrizeKit = renormKit;
renormSourceFile = FileNameJoin[{renormDirectory,renormConfig["SourceFile"]}];
renormSource = FromCharacterCode[BinaryReadList[renormSourceFile],"UTF-8"];
renormEssayFile = FileNameJoin[{renormDirectory,renormConfig["EssayFile"]}];
renormEssay = Import[renormEssayFile,"Text",CharacterEncoding->"UTF-8"];
renormStrings = StringCases[renormEssay,
  RegularExpression["LeanImportString\\[(\"(?:\\\\.|[^\"\\\\])*\")"] -> "$1"];
If[Length[renormStrings]!=1,Print[Failure["EmbeddedSourceCount",<||>]];Exit[1]];
renormHeldSource = ToExpression[First[renormStrings],InputForm,HoldComplete];
If[!MatchQ[renormHeldSource,HoldComplete[_String]] || First[renormHeldSource] =!= renormSource,
  Print[Failure["EmbeddedSourceMismatch",<||>]]; Exit[1]];
renormConverterFile = Quiet[Environment["RULE30_MARKDOWN_CONVERTER_SOURCE"]];
If[StringQ[renormConverterFile] && FileExistsQ[renormConverterFile],
  Get[renormConverterFile,CharacterEncoding->"UTF-8"]; renormConverter = MarkdownToNotebook,
  renormConverter = ResourceFunction["https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Function/MarkdownToNotebook"]];
renormOutput = FileNameJoin[{renormDirectory,"renormalization-essay.nb"}];
Clear[rule30Submission];
renormBuild = renormConverter[renormEssayFile,renormOutput,"UseCache"->False];
If[!FileExistsQ[renormOutput],Print[Failure["NotebookBuild",<||>]];Exit[1]];
renormEnvironmentNames = Select[Join[Names["Global`rule30Submission"],Names["MTNB$*`rule30Submission"]],
  ToExpression[#,InputForm,Function[s,ValueQ[s],HoldAll]]&];
If[Length[renormEnvironmentNames]!=1,Print[Failure["NotebookEnvironment",<||>]];Exit[1]];
renormEnvironment = ToExpression[First[renormEnvironmentNames]];
renormCheck = ToExpression[StringReplace[First[renormEnvironmentNames],
  "rule30Submission"~~EndOfString->"rule30KernelCheck"]];
If[!MatchQ[renormCheck,Success["KernelChecked",_Association]],Print[Failure["KernelReplay",<|"Check"->renormCheck|>]];Exit[1]];
renormHeadlines = renormConfig["Headlines"];
If[!AllTrue[renormHeadlines,renormEnvironment[#]["Kind"]==="theorem"&],Print[Failure["HeadlineKind",<||>]];Exit[1]];
renormAxioms = renormEnvironment[#]["Axioms"]&/@renormHeadlines;
If[!AllTrue[renormAxioms,ListQ[#] && Complement[#,{"propext","Classical.choice","Quot.sound"}]==={}&],
  Print[Failure["HeadlineAxioms",<||>]];Exit[1]];
renormNotebook = Get[renormOutput,CharacterEncoding->"UTF-8"];
renormInputs = Cases[renormNotebook,Cell[BoxData[b_],"Input",___]:>b,Infinity];
renormHeldInputs = ToExpression[#,StandardForm,HoldComplete]&/@renormInputs;
renormEmbedded = Cases[renormHeldInputs,HoldPattern[LeanImportString[s_String,___]]:>s,Infinity];
renormOutputs = Cases[renormNotebook,Cell[BoxData[b_],"Output",___]:>HoldComplete[b],Infinity];
renormMessages = Cases[renormNotebook,Cell[b_,"Message",___]:>HoldComplete[b],Infinity];
If[renormEmbedded=!={renormSource} || Length[renormMessages]!=0 || !StringContainsQ[ToString[renormOutputs,InputForm],"KernelChecked"],
  Print[Failure["SavedNotebookInspection",<|"Messages"->Length[renormMessages]|>]];Exit[1]];
renormReport = <|"NotebookBuilt"->True,"NotebookEvaluated"->True,
  "SavedSourceMatched"->True,"MessageCells"->0,"InputCells"->Length[renormInputs],
  "OutputCells"->Length[renormOutputs],"KernelCheckPassed"->True,
  "Declarations"->renormCheck[[2]]["Declarations"],"Headlines"->renormHeadlines,
  "AllHeadlineAxiomsStandard"->True,"PrizeAPISubmitted"->False,
  "StandaloneSHA256"->IntegerString[FileHash[renormSourceFile,"SHA256"],16,64],
  "NotebookSHA256"->IntegerString[FileHash[renormOutput,"SHA256"],16,64]|>;
Export[renormOutput<>".verification.json",renormReport,"RawJSON"];
Print[renormReport];
