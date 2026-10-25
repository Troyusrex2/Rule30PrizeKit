"""Release the generalized reader theorem and its unchanged full replay."""
import hashlib,json,shutil
from core import HERE,REPO

def main():
 dest=REPO/'research/agent-experiments/coordinator/20261024-seven';out=dest/'generic-absorbing-prefix';out.mkdir(exist_ok=False)
 module='Rule30GenericAbsorbingPrefixBarrierResearch';evidence='generic-absorbing-prefix-barrier-evidence-v1'
 r=json.loads((HERE/evidence/'report.json').read_text());assert r['check']['verdict']=='pass' and r['check']['replay']=={'constants':21,'ok':True} and not r['check']['newAxioms'];assert r['source_sha256']==hashlib.sha256((HERE/(module+'.lean')).read_bytes()).hexdigest();assert not (HERE/evidence/'build.log').read_text().strip()
 selected=[module+'.lean','build_generic_prefix_barrier_release.py']+[evidence+'/'+n for n in ['build.log','check.log','report.json']]
 for name in selected:
  target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(HERE/name,target)
 (out/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof\n',encoding='utf-8',newline='\n')
 shutil.copyfile(HERE/'GENERIC-ABSORBING-PREFIX-BARRIER.md',dest/'GENERIC-ABSORBING-PREFIX-BARRIER.md')
 files={p.relative_to(dest).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in out.rglob('*') if p.is_file()}
 manifest={'kit_commit':'3eca23c0a9fa6b153313655e6d51835406c2d06e','checker_sha256':'b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905','owned_replayed_declarations':21,'scope':'every natural-state reader absorbing on the specified prefix; every integer geometric scale >=1; actual finite past','full_problem_solved':False,'new_prize_submission':False,'files':dict(sorted(files.items()))}
 (dest/'generic-absorbing-prefix-artifacts.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n');print({'files':len(files),'bytes':sum((dest/n).stat().st_size for n in files),'owned_replayed_declarations':21})
if __name__=='__main__':main()
