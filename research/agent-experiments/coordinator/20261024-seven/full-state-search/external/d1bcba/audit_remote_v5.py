"""Independently replay the immutable public contribution on G913."""
import hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
root=Path.home()/'Rule30-offload';here=Path(__file__).resolve().parent;payload=root/'_cache/payload';sys.path.insert(0,str(payload))
from worker import guarded,sha
assert (here/'OWNER.txt').read_text().strip()=='Rule30 d1bcba independent full replay; 2026-10-25'
manifest=json.loads((here/'sources-v5.json').read_text())
for name,digest in manifest.items():assert sha(here/name)==digest,name
original=(here/'Rule30Submission.lean').read_bytes();first=original.splitlines(keepends=True)[0];stop=original.index(b'/-! ## 7. Instantaneous Invariants');assert (here/'ExternalFinitePsiBadClassV2AuditResearch.lean').read_bytes()==original[len(first):stop]+b'\nend Phase2\nend Rule30Submission\n'
base=json.loads((payload/'payload-manifest.json').read_text());ref=root/'reference'
assert base['kit_commit']=='3eca23c0a9fa6b153313655e6d51835406c2d06e'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ref,text=True).strip()==base['kit_commit']
assert sha(ref/'Check.lean')==base['checker_sha256']
module='ExternalFinitePsiBadClassV2AuditResearch';src=here/(module+'.lean');dest=ref/src.name
if dest.exists():assert dest.read_bytes()==src.read_bytes()
else:shutil.copyfile(src,dest)
own=ref/'.lake/build/lib/lean';lean=payload/'toolchain/bin/lean.exe';env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(own),str(ref/'lean/.lake/build/lib/lean'),str(payload/'toolchain/lib/lean')]);env['PYTHONUTF8']='1'
out=here/'badclass-evidence-g913-v2';out.mkdir(exist_ok=True);limits={'seconds':300,'rss_gib':24,'minimum_free_gib':16}
r={'external_id':'R30-20261025-d1bcba','authors':'Emerson Villafuerte; Antigravity (Google DeepMind)','source_sha256':sha(src),'kit_commit':base['kit_commit'],'checker_sha256':base['checker_sha256'],'machine_label':'G913','full_problem_solved':False}
r['build']=guarded([str(lean),'-o',str(own/(module+'.olean')),str(dest)],ref,env,out/'build.log',limits)
print({'build':r['build']},flush=True)
if r['build']['exit_code']==0 and not r['build']['guard_stop']:
 cmd=[str(lean),'--run','Check.lean',module,'--claim','partial']
 for h in ['Psi_enters_bad_of_finSupp','Psi_free_constraints_width6_of_finSupp']:cmd+=['--headline','Rule30Submission.'+h]
 r['replay']=guarded(cmd,ref,env,out/'check.log',limits)
 if r['replay']['exit_code']==0 and not r['replay']['guard_stop']:
  ck=json.loads([s for s in (out/'check.log').read_text().splitlines() if s.startswith('{')][-1]);assert ck['verdict']=='pass' and ck['replay']['ok'] and not ck['newAxioms'] and all(h['ok'] for h in ck['headlines']);r['check']=ck
assert sha(ref/'Check.lean')==base['checker_sha256']
(out/'report.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print({'all_passed':'check' in r,'constants':r.get('check',{}).get('replay',{}).get('constants')},flush=True)
sys.exit(0 if 'check' in r else 1)
