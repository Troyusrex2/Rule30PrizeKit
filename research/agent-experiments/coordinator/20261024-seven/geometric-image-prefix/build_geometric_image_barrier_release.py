"""Release the completed uniform integer-scale proof and exact full replay."""
import hashlib,json,shutil
from pathlib import Path
from core import HERE,REPO

def main():
 dest=REPO/'research/agent-experiments/coordinator/20261024-seven';out=dest/'geometric-image-prefix';out.mkdir(exist_ok=False)
 modules=[('Rule30WeightedSuffixPumpResearch','weighted-suffix-pump-evidence-v1',9),('Rule30FiniteImageBlackPumpResearch','finite-image-black-pump-evidence-v3',62),('Rule30GeometricImageConeResearch','geometric-image-cone-evidence-v1',23),('Rule30FinitePastGeometricRankObstructionResearch','finite-past-geometric-rank-evidence-v1',32)]
 selected={'build_geometric_image_barrier_release.py'}
 for mod,evidence,n in modules:
  r=json.loads((HERE/evidence/'report.json').read_text());assert r['check']['verdict']=='pass' and r['check']['replay']=={'constants':n,'ok':True} and not r['check']['newAxioms'];assert r['source_sha256']==hashlib.sha256((HERE/(mod+'.lean')).read_bytes()).hexdigest();assert not (HERE/evidence/'build.log').read_text().strip()
  selected.add(mod+'.lean');selected.update(evidence+'/'+name for name in ['build.log','check.log','report.json'])
 for name in sorted(selected):
  target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(HERE/name,target)
 (out/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof\n',encoding='utf-8',newline='\n')
 shutil.copyfile(HERE/'INTEGER-GEOMETRIC-FINITE-IMAGE-BARRIER.md',dest/'INTEGER-GEOMETRIC-FINITE-IMAGE-BARRIER.md')
 files={p.relative_to(dest).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in out.rglob('*') if p.is_file()}
 manifest={'kit_commit':'3eca23c0a9fa6b153313655e6d51835406c2d06e','checker_sha256':'b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905','owned_replayed_declarations':sum(n for _,_,n in modules),'scope':'all integer geometric scales >=1; signed costs; actual finite predecessors; fixed single-background reader','full_problem_solved':False,'new_prize_submission':False,'files':dict(sorted(files.items()))}
 (dest/'geometric-image-prefix-artifacts.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n');print({'files':len(files),'bytes':sum((dest/n).stat().st_size for n in files),'owned_replayed_declarations':manifest['owned_replayed_declarations']})
if __name__=='__main__':main()
