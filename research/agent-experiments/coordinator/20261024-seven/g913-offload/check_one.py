"""Guarded direct-Lean check of one explicitly named additional owned module."""
import argparse,json,os,shutil,sys
from datetime import datetime,timezone
from pathlib import Path
sys.stdout.reconfigure(encoding='utf-8')
sys.stderr.reconfigure(encoding='utf-8')

root=Path.home()/'Rule30-offload';payload=root/'_cache/payload';sys.path.insert(0,str(payload))
from worker import guarded,sha

p=argparse.ArgumentParser();p.add_argument('--module',required=True);p.add_argument('--headlines',nargs='+',required=True);a=p.parse_args()
assert a.module.isidentifier()
base=json.loads((payload/'payload-manifest.json').read_text());ref=root/'reference';src=root/'_cache'/(a.module+'.lean')
dest=ref/src.name
if dest.exists():assert dest.read_bytes()==src.read_bytes()
else:shutil.copyfile(src,dest)
assert sha(ref/'Check.lean')==base['checker_sha256']
own=ref/'.lake/build/lib/lean';lean=payload/'toolchain/bin/lean.exe';env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join([str(own),str(ref/'lean/.lake/build/lib/lean'),str(payload/'toolchain/lib/lean')])
folder=root/'results'/(datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+a.module);folder.mkdir(parents=True)
limits={'seconds':300,'rss_gib':4,'minimum_free_gib':16}
r={'module':a.module,'source_sha256':sha(src),'kit_commit':base['kit_commit'],'checker_sha256':base['checker_sha256'],'full_problem_solved':False}
r['build']=guarded([str(lean),'-o',str(own/(a.module+'.olean')),str(dest)],ref,env,folder/'build.log',limits)
if not r['build']['exit_code'] and not r['build']['guard_stop']:
    cmd=[str(lean),'--run','Check.lean',a.module,'--claim','partial']
    for h in a.headlines:cmd+=['--headline',a.module+'.'+h]
    r['replay']=guarded(cmd,ref,env,folder/'check.log',limits)
    if not r['replay']['exit_code'] and not r['replay']['guard_stop']:
        ck=json.loads([s for s in (folder/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
        assert ck['verdict']=='pass' and ck['replay']['ok'] and not ck['newAxioms'] and all(h['ok'] for h in ck['headlines'])
        r['check']=ck
assert sha(ref/'Check.lean')==base['checker_sha256']
(folder/'report.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print({'module':a.module,'pass':'check' in r,'report_relative':folder.relative_to(root).as_posix()},flush=True)
if 'check' not in r:print((folder/'build.log').read_text(encoding='utf-8')[-2500:],flush=True)
sys.exit(0 if 'check' in r else 1)
