(* Run in a fresh local Wolfram kernel, version 14.3 or later.
   Set RULE30PRIZE_KIT to a prepared pinned kit before starting that kernel.
   This script builds and checks the notebook. It never submits to the prize API. *)

$CharacterEncoding = "UTF-8";
If[$VersionNumber < 14.3, Print[Failure["KernelVersion", <|"Required" -> "14.3 or later"|>]]; Exit[1]];

If[PacletFind["Wolfram/LeanLink"] === {},
  PacletInstall["https://resources.wolframcloud.com/PacletRepository/pacletsitecontent/Paclets/Wolfram__LeanLink-1.2.1.paclet"]];
Needs["Wolfram`LeanLink`"];

suffixDirectory = DirectoryName[$InputFileName];
suffixConfigFile = Quiet[Environment["RULE30_NOTEBOOK_CONFIG"]];
If[StringQ[suffixConfigFile] && suffixConfigFile =!= "",
  If[!FileExistsQ[suffixConfigFile], Print[Failure["NotebookConfig", <|"File" -> suffixConfigFile|>]]; Exit[1]];
  suffixConfig = Import[suffixConfigFile, "RawJSON"];
  suffixContentDirectory = DirectoryName[ExpandFileName[suffixConfigFile]],
  suffixConfig = <|"SourceFile" -> "Rule30ColumnSeparationStandalone.lean",
    "EssayFile" -> "column-separation-essay.md",
    "Headlines" -> {"Rule30Submission.columns_distinguishable",
      "Rule30Submission.mirror_columns_distinguishable", "Rule30Submission.columns_injective"}|>;
  suffixContentDirectory = suffixDirectory];
If[!AssociationQ[suffixConfig] ||
  !And @@ (KeyExistsQ[suffixConfig, #] & /@ {"SourceFile", "EssayFile", "Headlines"}),
  Print[Failure["NotebookConfig", <|"Message" -> "SourceFile, EssayFile and Headlines are required."|>]]; Exit[1]];
suffixKit = Environment["RULE30PRIZE_KIT"];
If[!StringQ[suffixKit] || !DirectoryQ[suffixKit],
  Print[Failure["KitDirectory", <|"Message" -> "Set RULE30PRIZE_KIT before starting the kernel."|>]]; Exit[1]];
$Rule30PrizeKit = suffixKit;
suffixSourceFile = FileNameJoin[{suffixContentDirectory, suffixConfig["SourceFile"]}];
suffixSource = FromCharacterCode[BinaryReadList[suffixSourceFile], "UTF-8"];
suffixHeadlines = suffixConfig["Headlines"];
If[!ListQ[suffixHeadlines] || suffixHeadlines === {} || !AllTrue[suffixHeadlines, StringQ],
  Print[Failure["NotebookConfig", <|"Message" -> "Headlines must be a nonempty list of strings."|>]]; Exit[1]];

(* Verify the exact embedded source before evaluation. The notebook itself
   performs the module replay; a duplicate preflight retains another full native
   import graph and needlessly doubles peak memory. *)
suffixEssayFile = FileNameJoin[{suffixContentDirectory, suffixConfig["EssayFile"]}];
suffixEssayText = Import[suffixEssayFile, "Text", CharacterEncoding -> "UTF-8"];
suffixEmbeddedStrings = StringCases[suffixEssayText,
  RegularExpression["LeanImportString\\[(\"(?:\\\\.|[^\"\\\\])*\")"] -> "$1"];
If[Length[suffixEmbeddedStrings] =!= 1,
  Print[Failure["EmbeddedSourceMismatch", <||>]]; Exit[1]];
(* Parse the notebook's Wolfram string literal while holding all evaluation. *)
suffixHeldSource = ToExpression[First[suffixEmbeddedStrings], InputForm, HoldComplete];
If[!MatchQ[suffixHeldSource, HoldComplete[_String]] || First[suffixHeldSource] =!= suffixSource,
  Print[Failure["EmbeddedSourceMismatch", <||>]]; Exit[1]];

suffixOutput = Quiet[Environment["RULE30_NOTEBOOK_OUTPUT"]];
If[!StringQ[suffixOutput] || suffixOutput === "",
  suffixOutput = FileNameJoin[{suffixContentDirectory, FileBaseName[suffixConfig["EssayFile"]] <> ".nb"}]];
Clear[rule30Submission];
suffixConverterSource = Quiet[Environment["RULE30_MARKDOWN_CONVERTER_SOURCE"]];
If[StringQ[suffixConverterSource] && FileExistsQ[suffixConverterSource],
  Get[suffixConverterSource, CharacterEncoding -> "UTF-8"];
  suffixConverter = MarkdownToNotebook,
  suffixConverter = ResourceFunction[
    "https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Function/MarkdownToNotebook"]];
suffixBuild = suffixConverter[
  suffixEssayFile,
  suffixOutput, "UseCache" -> False];
If[!FileExistsQ[suffixOutput], Print[Failure["NotebookBuild", <|"Result" -> suffixBuild|>]]; Exit[1]];

(* The notebook must actually evaluate its own LeanImportString cell. *)
(* MarkdownToNotebook evaluates each document in a private MTNB$ context. Read
   its own result, rather than the separate preflight or an unbound Global symbol. *)
suffixEnvironmentNames = Select[Join[Names["Global`rule30Submission"], Names["MTNB$*`rule30Submission"]],
  ToExpression[#, InputForm, Function[s, ValueQ[s], HoldAll]] &];
If[Length[suffixEnvironmentNames] =!= 1,
  Print[Failure["NotebookEnvironment", <|"Count" -> Length[suffixEnvironmentNames]|>]]; Exit[1]];
suffixNotebookEnvironment = ToExpression[First[suffixEnvironmentNames]];
suffixCheckName = StringReplace[First[suffixEnvironmentNames],
  "rule30Submission" ~~ EndOfString -> "rule30KernelCheck"];
suffixNotebookCheck = ToExpression[suffixCheckName];
If[!MatchQ[suffixNotebookCheck, Success["KernelChecked", _Association]],
  Print[Failure["NotebookEvaluation", <|"Check" -> suffixNotebookCheck|>]]; Exit[1]];
suffixHeadlineAxioms = Table[suffixNotebookEnvironment[name]["Axioms"], {name, suffixHeadlines}];
If[!AllTrue[Table[suffixNotebookEnvironment[name]["Kind"], {name, suffixHeadlines}], # === "theorem" &],
  Print[Failure["HeadlineKind", <||>]]; Exit[1]];
If[!AllTrue[suffixHeadlineAxioms, Function[axioms, ListQ[axioms] &&
    Complement[axioms, {"propext", "Classical.choice", "Quot.sound"}] === {}]],
  Print[Failure["HeadlineAxioms", <||>]]; Exit[1]];
suffixReport = <|"NotebookBuilt" -> True, "NotebookEvaluated" -> True,
  "LeanKernelChecksPassed" -> True, "PrizeAPISubmitted" -> False,
  "KernelVersion" -> $Version,
  "StandaloneFileSHA256" -> IntegerString[FileHash[suffixSourceFile, "SHA256"], 16, 64],
  "EmbeddedSourceMatched" -> True,
  "KernelReplayedModule" -> suffixNotebookCheck[[2]]["Module"],
  "KernelReplayedDeclarations" -> suffixNotebookCheck[[2]]["Declarations"],
  "AllHeadlineAxiomsStandard" -> True,
  "Headlines" -> suffixHeadlines|>;
Export[suffixOutput <> ".verification.json", suffixReport, "RawJSON"];
Print[suffixReport];
