"""Independent guarded leaf checks, resumed by exact source and object hashes."""
import argparse,hashlib,json,os,shutil,subprocess,sys,threading
from concurrent.futures import ThreadPoolExecutor,as_completed
from pathlib import Path

root=Path.home()/'Rule30-offload';payload=root/'_cache/payload';sys.path.insert(0,str(payload))
from worker import guarded,sha

def main():
    p=argparse.ArgumentParser();p.add_argument('--limit',type=int);a=p.parse_args();control=Path(__file__).resolve().parent
    manifest=json.loads((control/'batch-manifest.json').read_text());base=json.loads((payload/'payload-manifest.json').read_text())
    for name,digest in manifest['files'].items():assert sha(control/name)==digest,name
    ref=root/'reference';assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ref,text=True).strip()==base['kit_commit']
    assert sha(ref/'Check.lean')==base['checker_sha256']
    own=ref/'.lake/build/lib/lean';lean=payload/'toolchain/bin/lean.exe';env=os.environ.copy()
    env['LEAN_PATH']=os.pathsep.join([str(own),str(ref/'lean/.lake/build/lib/lean'),str(payload/'toolchain/lib/lean')])
    out=root/'results/budget8-c600';out.mkdir(parents=True,exist_ok=True)
    def one(rec):
        m=rec['module'];src=control/rec['source'];dest=ref/(m+'.lean');folder=out/m;folder.mkdir(exist_ok=True)
        if dest.exists():assert dest.read_bytes()==src.read_bytes(),m
        else:shutil.copyfile(src,dest)
        report=folder/'report.json';obj=own/(m+'.olean')
        if report.exists():
            r=json.loads(report.read_text())
            if r.get('check',{}).get('verdict')=='pass' and obj.exists():
                assert r['source_sha256']==sha(src) and r['kit_commit']==base['kit_commit']
                assert all(sha(own/name)==digest for name,digest in r['object_hashes'].items())
                print({'module':m,'stage':'retained_exact_full_replay'},flush=True);return r
        r={'module':m,'source_sha256':sha(src),'kit_commit':base['kit_commit'],'checker_sha256':base['checker_sha256'],
           'machine_label':'G913','full_problem_solved':False}
        print({'module':m,'stage':'compile'},flush=True)
        r['build']=guarded([str(lean),'-o',str(obj),str(dest)],ref,env,folder/'build.log',manifest['limits'])
        report.write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
        if r['build']['exit_code'] or r['build']['guard_stop']:return r
        argv=[str(lean),'--run','Check.lean',m,'--claim','partial']
        for h in rec['headlines']:argv+=['--headline',m+'.'+h]
        print({'module':m,'stage':'full_kernel_replay'},flush=True)
        r['replay']=guarded(argv,ref,env,folder/'check.log',manifest['limits'])
        if not r['replay']['exit_code'] and not r['replay']['guard_stop']:
            ck=json.loads([s for s in (folder/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
            assert ck['verdict']=='pass' and ck['replay']['ok'] and not ck['newAxioms'] and all(h['ok'] for h in ck['headlines'])
            r['check']=ck;r['object_hashes']={f.name:sha(f) for f in own.glob(m+'.olean*')}
        report.write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
        print({'module':m,'pass':'check' in r,'build_s':r['build']['seconds'],'replay_s':r['replay']['seconds']},flush=True)
        return r
    helper=one(manifest['helper']);assert 'check' in helper,'Prefix helper failed'
    requested=manifest['modules'] if a.limit is None else manifest['modules'][:a.limit];done=[];failed=[]
    summary={'budget':8,'horizon':102,'total_leaf_modules':len(manifest['modules']),'requested_leaf_modules':len(requested),
      'kit_commit':base['kit_commit'],'checker_sha256':base['checker_sha256'],'workers':manifest['workers'],
      'completed':done,'failed':failed,'full_problem_solved':False,'certificate_complete':False}
    def write():
        temp=out/'progress.tmp';temp.write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8');temp.replace(out/'progress.json')
    write()
    with ThreadPoolExecutor(max_workers=manifest['workers']) as pool:
        futures={pool.submit(one,rec):rec['module'] for rec in requested}
        for future in as_completed(futures):
            r=future.result();(done if 'check' in r else failed).append(r['module']);write()
            print({'completed':len(done),'failed':len(failed),'requested':len(requested)},flush=True)
    if failed:sys.exit(1)
    if a.limit is not None and len(requested)<len(manifest['modules']):
        print({'stage':'requested_calibration_complete','leaves_passed':len(done),'root_not_claimed':True},flush=True);return
    r=one(manifest['root']);summary['root_passed']='check' in r;summary['certificate_complete']='check' in r;write()
    assert sha(ref/'Check.lean')==base['checker_sha256']
    if 'check' not in r:sys.exit(1)
    print({'budget8_full_kernel_certificate':'pass','leaf_modules':len(done)},flush=True)

if __name__=='__main__':main()
