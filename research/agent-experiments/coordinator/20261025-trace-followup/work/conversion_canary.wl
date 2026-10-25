root=DirectoryName[$InputFileName];
dir=FileNameJoin[{root,"essay"}];
$CloudConnected;
md2nb=ResourceFunction["https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Function/MarkdownToNotebook"];
result=md2nb[FileNameJoin[{dir,"canary.md"}],FileNameJoin[{dir,"canary.nb"}],"UseCache"->False];
If[!FileExistsQ[FileNameJoin[{dir,"canary.nb"}]],Print["Canary notebook missing"];Exit[2]];
nb=Import[FileNameJoin[{dir,"canary.nb"}],"NB"];
iconized=!FreeQ[nb,"IconizedObject"];
inputs=Cases[nb,Cell[BoxData[b_],"Input",___]:>b,Infinity];
held=ToExpression[#,StandardForm,HoldComplete]&/@inputs;
literal=Cases[held,HoldPattern[Set[sourceMarker,s_String]]:>s,Infinity];
outputs=Cases[nb,Cell[BoxData[b_],"Output",___]:>ToExpression[b,StandardForm,HoldComplete],Infinity];
expectedOutputs={HoldComplete[30],HoldComplete[4]};
ok=TrueQ[iconized]&&Length[inputs]===2&&literal==={"canary source: forall n, n = n"}&&outputs===expectedOutputs;
record=<|"pass"->ok,"sourceIconized"->iconized,"inputCells"->Length[inputs],
 "literalRoundTrip"->(literal==={"canary source: forall n, n = n"}),
 "converterEvaluatedCells"->(outputs===expectedOutputs),"callerControlAssigned"->(canaryControl===4),"UseCache"->False,
 "LeanProofEvaluated"->False,"prizeNotebookValidated"->False,"submitted"->False|>;
Export[FileNameJoin[{dir,"conversion-canary.json"}],record,"RawJSON"];
Print[ExportString[record,"RawJSON"]];
Exit[If[TrueQ[ok],0,3]];
