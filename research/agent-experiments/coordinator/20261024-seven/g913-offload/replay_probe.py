"""Retry only the already-built probe with an explicit larger remote RAM budget."""
import hashlib,json,os,sys
from datetime import datetime,timezone
from pathlib import Path

root=Path.home()/'Rule30-offload';payload=root/'_cache/payload';sys.path.insert(0,str(payload))
from worker import guarded,sha

manifest=json.loads((payload/'payload-manifest.json').read_text())
ref=root/'reference';m=manifest['probe'];src=payload/'sources'/(m+'.lean')
assert sha(src)==manifest['files']['sources/'+m+'.lean']
assert sha(ref/'Check.lean')==manifest['checker_sha256'] and src.read_bytes()==(ref/src.name).read_bytes()
own=ref/'.lake/build/lib/lean';cached=ref/'lean/.lake/build/lib/lean';lean=payload/'toolchain/bin/lean.exe'
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(own),str(cached),str(payload/'toolchain/lib/lean')])
out=root/'results'/(datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-replay24');out.mkdir(parents=True)
objects={p.name:sha(p) for p in own.glob(m+'.olean*')};assert m+'.olean' in objects
limits={'seconds':300,'rss_gib':24,'minimum_free_gib':16}
r={'machine_label':'G913','module':m,'kit_commit':manifest['kit_commit'],'source_sha256':sha(src),
   'checker_sha256':manifest['checker_sha256'],'object_hashes':objects,'full_problem_solved':False}
r['replay']=guarded([str(lean),'--run','Check.lean',m,'--claim','partial','--headline',m+'.cert'],
    ref,env,out/'check.log',limits)
if r['replay']['exit_code']==0 and not r['replay']['guard_stop']:
    ck=json.loads([s for s in (out/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert ck['verdict']=='pass' and ck['replay']['ok'] and not ck['newAxioms'] and all(h['ok'] for h in ck['headlines'])
    r['check']=ck
assert sha(ref/'Check.lean')==manifest['checker_sha256']
(out/'report.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print({'report_relative':out.relative_to(root).as_posix(),'pass':'check' in r,'resources':r['replay']},flush=True)
sys.exit(0 if 'check' in r else 1)
