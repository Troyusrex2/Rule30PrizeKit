Needs["Wolfram`LeanLink`"];
root=DirectoryName[$InputFileName];
$Rule30PrizeKit=Environment["RULE30PRIZE_KIT"];
source=FromCharacterCode[BinaryReadList[FileNameJoin[{root,"Rule30Submission.lean"}]],"UTF-8"];
review=Import[FileNameJoin[{root,"essay-review.md"}],"Text",CharacterEncoding->"UTF-8"];
Print["Importing the embedded standalone proof"];
rule30Submission=LeanImportString[source,"ProjectDir"->$Rule30PrizeKit];
If[!MatchQ[rule30Submission,_LeanEnvironment],Print["LeanImportString failed"];Exit[2]];
checkCode="formalHeadline = rule30Submission[\"Rule30Submission.theta_explicit_large_periods\"];\nformalType = formalHeadline[\"TypeForm\"];\nformalAxioms = formalHeadline[\"Axioms\"];\nformalKernelCheck = formalHeadline[\"KernelCheck\"];\n{formalType, formalAxioms, formalKernelCheck}";
Print["Running full LeanLink kernel replay"];
formalResult=ToExpression[checkCode];
If[!MatchQ[formalKernelCheck,_Success],Print[InputForm[formalKernelCheck]];Exit[3]];
inputCell[code_String]:=Cell[BoxData[code],"Input"];
proofCell=Cell[BoxData[RowBox[{"rule30Submission","=",RowBox[{"LeanImportString","[",
  ToBoxes[Iconize[source,"Lean source"]],",",RowBox[{"\"ProjectDir\"","->","$Rule30PrizeKit"}],"]"}]}]],"Input"];
heldProof=ToExpression[proofCell[[1,1]],StandardForm,HoldComplete];
extracted=Cases[heldProof,HoldPattern[LeanImportString[s_String,___]]:>s,Infinity];
If[extracted=!={source},Print["Embedded source did not round-trip"];Exit[4]];
patternCode="pattern = CellularAutomaton[30, {{1}, 0}, 40];\nImageResize[Image[1-pattern, \"Bit\"], 486, Resampling -> \"Nearest\"]";
patternImage=ToExpression[patternCode];
Export[FileNameJoin[{root,"essay-pattern.png"}],patternImage];
centerCode="centerPrefix = pattern[[All, Ceiling[Length[First[pattern]]/2]]];\nStringJoin[ToString /@ centerPrefix]";
centerText=ToExpression[centerCode];
previewCode="Clear[delayedInput, delayedRow];\ndelayedInput[j_, t_] := If[t == 8*j+5, 1, Boole[Mod[t, 4] != 1]];\ndelayedRow[j_, depth_] := Module[{mu=8*j+8, w=8*j+12, cols, p, c, next},\n  cols = {ConstantArray[0,w], Table[delayedInput[j,t],{t,0,w-1}]};\n  Do[p=cols[[-2]]; c=cols[[-1]];\n    next=Table[BitXor[c[[If[t+1<w,t+2,mu+1]]],BitOr[c[[t+1]],p[[t+1]]]],{t,0,w-1}];\n    AppendTo[cols,next],{depth-1}];\n  First /@ cols];\npreview = Table[delayedRow[j,160],{j,0,4}];\nImageResize[Image[1-preview, \"Bit\"], {644,120}, Resampling -> \"Nearest\"]";
previewImage=ToExpression[previewCode];
Export[FileNameJoin[{root,"essay-preview.png"}],previewImage];
lemmas={"theta_delay_lt_pow_period","theta_spatial_periodic","free_formula","free_no_010110","free_no_1011010"};
lemmaCode="AssociationMap[rule30Submission[\"Rule30Submission.\"<>#][\"TypeForm\"]&, {\"theta_delay_lt_pow_period\",\"theta_spatial_periodic\",\"free_formula\",\"free_no_010110\",\"free_no_1011010\"}]";
lemmaTypes=ToExpression[lemmaCode];
paragraphs=Select[StringSplit[review,"\n\n"],StringLength[#]>0&];
textCells=Cell[#,"Text"]&/@Drop[paragraphs,2];
nb=Notebook[Join[{
 Cell["One delayed defect forces unbounded spatial periods in Rule 30 reconstruction","Title"],
 Cell["Troy Lowry, with OpenAI Codex","Author"],
 Cell["Draft for human review. Partial result; not a solution to a prize problem. No API submission has been made.","Abstract"],
 Cell["The question and the single-seed pattern","Section"],
 inputCell[patternCode],Cell[BoxData[ToBoxes[patternImage]],"Output"],
 inputCell[centerCode],Cell[BoxData[ToBoxes[centerText]],"Output"],
 Cell["Exploration: delaying one allowed defect","Section"],
 Cell["The five bands below show j=0 through j=4, read left to right in spatial depth 0 through 160. Black pixels denote black cells.","Text"],
 inputCell[previewCode],Cell[BoxData[ToBoxes[previewImage]],"Output"],
 Cell["Claim and proof","Section"]},textCells,{
 Cell["The embedded formal proof","Section"],
 inputCell["Needs[\"Wolfram`LeanLink`\"];\n$Rule30PrizeKit = Environment[\"RULE30PRIZE_KIT\"];"],
 proofCell,Cell[BoxData[ToBoxes[Head[rule30Submission]]],"Output"],
 Cell["Full kernel check and headline type","Section"],
 inputCell[checkCode],Cell[BoxData[ToBoxes[formalResult]],"Output"],
 Cell["Essential lemma statements","Section"],
 inputCell[lemmaCode],Cell[BoxData[ToBoxes[lemmaTypes]],"Output"],
 Cell["Limits","Section"],
 Cell["Each member is spatially periodic. Unboundedness is across synthetic inputs. No actual finite-right realizability, black-density bound, critical-charge bound, absorption result or canonical center nonperiodicity is proved.","Text"],
 Cell["References","Section"],
 Cell[TextData[{"Official catalog proposal: ",Hyperlink["PR25","https://github.com/WolframInstitute/Rule30PrizeKit/pull/25"]}],"Text"]}],
 StyleDefinitions->"Default.nb",TaggingRules-><|"Claim"->"partial","Problem"->1,"Submitted"->False,
  "KitCommit"->"0090056412733accaa27643d3cbbf982104f2251"|>];
Put[nb,FileNameJoin[{root,"delayed-defect-essay.nb"}]];
metadata=<|"built"->True,"submitted"->False,"isLeanEnvironment"->True,
 "kernelCheckSuccess"->True,"kernelCheck"->ToString[formalKernelCheck,InputForm],
 "axioms"->ToString[formalAxioms,InputForm],"sourceRoundTrip"->True,
 "sourceSHA256"->FileHash[FileNameJoin[{root,"Rule30Submission.lean"}],"SHA256","HexString"],
 "notebookSHA256"->FileHash[FileNameJoin[{root,"delayed-defect-essay.nb"}],"SHA256","HexString"],
 "inputCells"->Length[Cases[nb,Cell[_,"Input",___],Infinity]]|>;
Export[FileNameJoin[{root,"essay-build.json"}],metadata,"RawJSON"];
Print[ExportString[metadata,"RawJSON"]];
Exit[0];
