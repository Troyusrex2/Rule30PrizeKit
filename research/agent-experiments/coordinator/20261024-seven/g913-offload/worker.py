"""Run exact Lean sources on the remote host with explicit resource accounting."""
import argparse,hashlib,json,os,shutil,subprocess,sys,time
from datetime import datetime,timezone
from pathlib import Path
import psutil

def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

def guarded(argv,cwd,env,log,limits):
    start=time.monotonic();peak=0;minfree=psutil.virtual_memory().available;reason=None
    with log.open('w',encoding='utf-8') as out:
        process=subprocess.Popen(argv,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT)
        owner=psutil.Process(process.pid)
        while process.poll() is None:
            try:members=[owner]+owner.children(recursive=True)
            except psutil.NoSuchProcess:members=[]
            rss=0
            for p in members:
                try:rss+=p.memory_info().rss
                except psutil.NoSuchProcess:pass
            peak=max(peak,rss);free=psutil.virtual_memory().available;minfree=min(minfree,free)
            if time.monotonic()-start>limits['seconds']:reason='time_guard'
            elif rss>limits['rss_gib']*2**30:reason='rss_guard'
            elif free<limits['minimum_free_gib']*2**30:reason='free_memory_guard'
            if reason:
                for p in reversed(members):
                    try:p.kill()
                    except psutil.NoSuchProcess:pass
                process.wait();break
            time.sleep(.05)
    r={'exit_code':process.returncode,'seconds':round(time.monotonic()-start,3),
       'peak_tree_rss_gib':round(peak/2**30,3),'minimum_free_gib':round(minfree/2**30,3),
       'guard_stop':reason,'limits':limits}
    log.with_suffix('.resources.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
    return r

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True)
    p.add_argument('--probe',action='store_true');a=p.parse_args();root=a.root.resolve();payload=Path(__file__).resolve().parent
    manifest=json.loads((payload/'payload-manifest.json').read_text(encoding='utf-8'))
    for name,digest in manifest['files'].items():assert sha(payload/name)==digest,name
    ref=root/'reference'
    if not ref.exists():subprocess.run(['git','clone',str(payload/'kit.bundle'),str(ref)],check=True)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ref,text=True).strip()==manifest['kit_commit']
    assert sha(ref/'Check.lean')==manifest['checker_sha256']
    cached=ref/'lean/.lake/build/lib/lean';cached.mkdir(parents=True,exist_ok=True)
    shutil.copytree(payload/'compiled',cached,dirs_exist_ok=True)
    own=ref/'.lake/build/lib/lean';own.mkdir(parents=True,exist_ok=True)
    lean=payload/'toolchain/bin/lean.exe';env=os.environ.copy()
    env['LEAN_PATH']=os.pathsep.join([str(own),str(cached),str(payload/'toolchain/lib/lean')])
    version=subprocess.check_output([str(lean),'--version'],env=env,text=True).strip();assert '4.35.0' in version
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ');out=root/'results'/stamp;out.mkdir(parents=True)
    heads={'Rule30GoldenDFAResearch':['run_lt'],'Rule30GoldenEvenSupportResearch':['step_matches'],
      'Rule30GoldenBudgetResearch':['uniform_width_of_all_budget_checks'],'Rule30GoldenBudgetDFSResearch':['dfs_sound'],
      'Rule30GoldenPackedBitsResearch':['bits_pack_project'],'Rule30GoldenPackedBudgetResearch':['dfs_sound'],
      'Rule30GoldenCompactCodecResearch':['getUsed_encode'],'Rule30GoldenCompactBudgetResearch':['dfs_sound'],
      'Rule30GoldenCompactSmokeResearch':['initial_run_boundary','one_black_boundary','two_black_boundary','small_frontier_compact_agree'],
      manifest['probe']:['cert']}
    modules=manifest['modules'] if a.probe else manifest['modules'][:-1];records=[]
    summary={'machine_label':'G913','kit_commit':manifest['kit_commit'],'checker_sha256':manifest['checker_sha256'],
        'lean_version':version,'direct_lean_with_pinned_imports':True,'records':records,'full_problem_solved':False}
    report=out/'report.json'
    for m in modules:
        src=payload/'sources'/(m+'.lean');target=ref/src.name
        if target.exists():assert target.read_bytes()==src.read_bytes(),m
        else:shutil.copyfile(src,target)
        r={'module':m,'source_sha256':sha(src)};records.append(r)
        print({'module':m,'stage':'compile'},flush=True)
        r['build']=guarded([str(lean),'-o',str(own/(m+'.olean')),str(target)],ref,env,out/(m+'.build.log'),manifest['remote_guard'])
        report.write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
        if r['build']['exit_code'] or r['build']['guard_stop']:sys.exit(1)
        argv=[str(lean),'--run','Check.lean',m,'--claim','partial']
        for h in heads[m]:argv+=['--headline',m+'.'+h]
        print({'module':m,'stage':'full_kernel_replay'},flush=True)
        r['replay']=guarded(argv,ref,env,out/(m+'.check.log'),manifest['remote_guard'])
        if r['replay']['exit_code']==0 and not r['replay']['guard_stop']:
            ck=json.loads([s for s in (out/(m+'.check.log')).read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
            assert ck['verdict']=='pass' and ck['replay']['ok'] and not ck['newAxioms'] and all(h['ok'] for h in ck['headlines'])
            r['check']=ck
        report.write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
        if 'check' not in r:sys.exit(1)
        print({'module':m,'verdict':'pass','constants':r['check']['replay']['constants'],
            'build_peak_gib':r['build']['peak_tree_rss_gib'],'replay_peak_gib':r['replay']['peak_tree_rss_gib']},flush=True)
    summary['all_requested_modules_passed']=True
    assert sha(ref/'Check.lean')==manifest['checker_sha256']
    report.write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8');print({'report_relative':report.relative_to(root).as_posix(),'all_passed':True},flush=True)

if __name__=='__main__':main()
