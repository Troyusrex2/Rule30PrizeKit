from pathlib import Path
import os,re,subprocess
root=Path(__file__).resolve().parent;out=root/'essay-combined'
md=(out/'essay.md').read_text(encoding='utf-8')
cells=re.findall(r'```wl\s*\n(.*?)\n```',md,re.S);assert len(cells)==7
code='\n'.join(cells[:3])+'''
If[finiteGapControl=!={0,1}||resetPrefix=!={1,0,0,0,0}||
 !StringStartsQ[StringJoin[ToString/@centerPrefix],"1101110011000101"],
 Print["Exploration control failed"];Exit[2]];
record=<|"pass"->True,"finiteGapControl"->finiteGapControl,"resetPrefix"->resetPrefix,
 "centerPrefixControl"->True,"proofCellsExecuted"->False,"freshNotebookVerified"->False|>;
Export["'''+(out/'exploration-controls.json').as_posix()+'''",record,"RawJSON"];
Print[ExportString[record,"RawJSON"]];Exit[0];
'''
script=root/'exploration_controls.wl';script.write_text(code,encoding='utf-8',newline='\n')
engine=Path(r'C:\Program Files\Wolfram Research\Wolfram Engine\15.0\wolfram.exe')
launch='$HistoryLength=0; Get["'+script.as_posix()+'",CharacterEncoding->"UTF-8"]; Quit[]'
r=subprocess.run([str(engine),'-noprompt','-run',launch],cwd=root,env=dict(os.environ,PYTHONUTF8='1'),capture_output=True)
(out/'exploration-controls-wolfram.log').write_bytes(r.stdout+r.stderr)
print((r.stdout+r.stderr).decode('utf-8',errors='replace'),flush=True);r.check_returncode()
