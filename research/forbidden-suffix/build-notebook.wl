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
  suffixConfig = <|"SourceFile" -> "Rule30SuffixStandalone.lean",
    "EssayFile" -> "Rule30-Forbidden-Suffix-Addendum.md",
    "Headlines" -> {"Rule30Submission.no_padding_suffix011",
      "Rule30Submission.no_padding_suffix001001", "Rule30Submission.no_padding_suffix111001"}|>;
  suffixContentDirectory = suffixDirectory];
If[!AssociationQ[suffixConfig] ||
  !And @@ (KeyExistsQ[suffixConfig, #] & /@ {"SourceFile", "EssayFile", "Headlines"}),
  Print[Failure["NotebookConfig", <|"Message" -> "SourceFile, EssayFile and Headlines are required."|>]]; Exit[1]];
suffixKit = Environment["RULE30PRIZE_KIT"];
If[!StringQ[suffixKit] || !DirectoryQ[suffixKit],
  Print[Failure["KitDirectory", <|"Message" -> "Set RULE30PRIZE_KIT before starting the kernel."|>]]; Exit[1]];
$Rule30PrizeKit = suffixKit;
suffixSourceFile = FileNameJoin[{suffixContentDirectory, suffixConfig["SourceFile"]}];
suffixSource = "import Rule30PrizeKit\n" <> Import[suffixSourceFile, "Text", CharacterEncoding -> "UTF-8"];
suffixHeadlines = suffixConfig["Headlines"];
If[!ListQ[suffixHeadlines] || suffixHeadlines === {} || !AllTrue[suffixHeadlines, StringQ],
  Print[Failure["NotebookConfig", <|"Message" -> "Headlines must be a nonempty list of strings."|>]]; Exit[1]];

(* Preflight checks the exact source used by the notebook, including its root import. *)
suffixPreflight = LeanImportString[suffixSource, "ProjectDir" -> suffixKit];
suffixPreflightChecks = Table[suffixPreflight[name]["KernelCheck"], {name, suffixHeadlines}];
If[!AllTrue[suffixPreflightChecks, MatchQ[#, _Success] &],
  Print[Failure["LeanPreflight", <|"Checks" -> suffixPreflightChecks|>]]; Exit[1]];

suffixOutput = Quiet[Environment["RULE30_NOTEBOOK_OUTPUT"]];
If[!StringQ[suffixOutput] || suffixOutput === "",
  suffixOutput = FileNameJoin[{suffixContentDirectory, FileBaseName[suffixConfig["EssayFile"]] <> ".nb"}]];
Clear[rule30Submission];
suffixConverter = ResourceFunction[
  "https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Function/MarkdownToNotebook"];
suffixBuild = suffixConverter[
  FileNameJoin[{suffixContentDirectory, suffixConfig["EssayFile"]}],
  suffixOutput, "UseCache" -> False];
If[!FileExistsQ[suffixOutput], Print[Failure["NotebookBuild", <|"Result" -> suffixBuild|>]]; Exit[1]];

(* The notebook must actually evaluate its own LeanImportString cell. *)
suffixNotebookChecks = Table[rule30Submission[name]["KernelCheck"], {name, suffixHeadlines}];
If[!AllTrue[suffixNotebookChecks, MatchQ[#, _Success] &],
  Print[Failure["NotebookEvaluation", <|"Checks" -> suffixNotebookChecks|>]]; Exit[1]];
suffixReport = <|"NotebookBuilt" -> True, "NotebookEvaluated" -> True,
  "LeanKernelChecksPassed" -> True, "PrizeAPISubmitted" -> False,
  "KernelVersion" -> $Version,
  "StandaloneFileSHA256" -> IntegerString[FileHash[suffixSourceFile, "SHA256"], 16, 64],
  "Headlines" -> suffixHeadlines|>;
Export[suffixOutput <> ".verification.json", suffixReport, "RawJSON"];
Print[suffixReport];
