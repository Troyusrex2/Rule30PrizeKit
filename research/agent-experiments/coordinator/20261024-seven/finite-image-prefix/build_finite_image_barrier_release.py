"""Release only final checked proofs and complete, corrected experiment batches."""
import hashlib,json,shutil
from pathlib import Path
from core import HERE,REPO

def main():
 dest=REPO/'research/agent-experiments/coordinator/20261024-seven';out=dest/'finite-image-prefix';out.mkdir(exist_ok=False)
 modules=[('Rule30FiniteWordAppendResearch','finite-word-append-evidence-v2',18),('Rule30FiniteImagePumpResearch','finite-image-pump-evidence-v7',123),('Rule30FinitePastPrefixRankObstructionResearch','finite-past-prefix-rank-evidence-v3',59)]
 selected={'build_finite_image_barrier_release.py'}
 for mod,evidence,n in modules:
  r=json.loads((HERE/evidence/'report.json').read_text());assert r['check']['verdict']=='pass' and r['check']['replay']=={'constants':n,'ok':True} and not r['check']['newAxioms'];assert r['source_sha256']==hashlib.sha256((HERE/(mod+'.lean')).read_bytes()).hexdigest()
  selected.add(mod+'.lean');selected.update(evidence+'/'+name for name in ['build.log','check.log','report.json'])
 for folder,expected in [('left-finite-history-v2',6),('left-future-phase',6),('inverse-clock-flux',8),('inverse-flux-rate',6)]:
  guards=json.loads((HERE/folder/'guard-report.json').read_text());assert len(guards['records'])==expected and all(r.get('exit_code')==0 and not r.get('guard_stop') and 'harness_exception' not in r for r in guards['records'])
  for p in (HERE/folder).iterdir():
   if p.is_file() and (p.suffix in ['.py','.json','.md'] or p.name=='OWNER.txt'):selected.add(folder+'/'+p.name)
 for name in sorted(selected):
  src=HERE/name;target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target)
 (out/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof\n',encoding='utf-8',newline='\n')
 shutil.copyfile(HERE/'FINITE-IMAGE-PREFIX-BARRIER.md',dest/'FINITE-IMAGE-PREFIX-BARRIER.md')
 files={p.relative_to(dest).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in out.rglob('*') if p.is_file()}
 manifest={'kit_commit':'3eca23c0a9fa6b153313655e6d51835406c2d06e','checker_sha256':'b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905','owned_replayed_declarations':sum(n for _,_,n in modules),'completed_numerical_cases':26,'full_problem_solved':False,'new_prize_submission':False,'files':dict(sorted(files.items()))}
 (dest/'finite-image-prefix-artifacts.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n');print({'files':len(files),'bytes':sum((dest/n).stat().st_size for n in files),'owned_replayed_declarations':manifest['owned_replayed_declarations']})
if __name__=='__main__':main()
