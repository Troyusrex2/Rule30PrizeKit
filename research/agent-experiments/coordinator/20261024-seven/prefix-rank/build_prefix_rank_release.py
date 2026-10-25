"""Allowlisted completed sources and evidence; never change old releases."""
import hashlib,json,shutil
from pathlib import Path
from core import HERE,REPO

def main():
 dest=REPO/'research/agent-experiments/coordinator/20261024-seven';out=dest/'prefix-rank'
 assert not (dest/'prefix-rank-artifacts.json').exists(),'Refuse to overwrite a completed release'
 out.mkdir(exist_ok=True)
 modules=[('Rule30WeightedWordPumpResearch','weighted-word-pump-evidence-v3',54),('Rule30FiniteLeftWordResearch','finite-left-word-evidence',30),('Rule30VacuumPrefixRankObstructionResearch','vacuum-prefix-rank-obstruction-evidence-v2',45),('Rule30FinitePastFrontResearch','finite-past-front-evidence-v2',15)]
 selected={'build_prefix_rank_release.py','vacuum-prefix-obstruction-data-v2.json'}
 for module,evidence,n in modules:
  report=json.loads((HERE/evidence/'report.json').read_text());assert report['check']['verdict']=='pass' and report['check']['replay']=={'constants':n,'ok':True};assert report['source_sha256']==hashlib.sha256((HERE/(module+'.lean')).read_bytes()).hexdigest()
  selected.add(module+'.lean')
  selected.update(evidence+'/'+name for name in ['report.json','build.log','check.log'])
 selected.update('left-finite-past/'+p.name for p in (HERE/'left-finite-past').iterdir() if p.is_file() and (p.suffix in ['.py','.json','.md'] or p.name=='OWNER.txt'))
 guards=json.loads((HERE/'left-finite-past/guard-report.json').read_text());assert len(guards['records'])==6 and all(r['exit_code']==0 and not r['guard_stop'] for r in guards['records'])
 for name in sorted(selected):
  src=HERE/name;target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target)
 (out/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof\n',encoding='utf-8',newline='\n')
 report=(HERE/'PREFIX-RANK-FINITE-PAST.md').read_bytes();(dest/'PREFIX-RANK-FINITE-PAST.md').write_bytes(report)
 files={p.relative_to(dest).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in out.rglob('*') if p.is_file()}
 manifest={'kit_commit':'3eca23c0a9fa6b153313655e6d51835406c2d06e','checker_sha256':'b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905','owned_replayed_declarations':sum(n for _,_,n in modules),'full_problem_solved':False,'new_prize_submission':False,'files':dict(sorted(files.items()))}
 (dest/'prefix-rank-artifacts.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n');print({'files':len(files),'bytes':sum((dest/n).stat().st_size for n in files),'owned_replayed_declarations':manifest['owned_replayed_declarations']})
if __name__=='__main__':main()
