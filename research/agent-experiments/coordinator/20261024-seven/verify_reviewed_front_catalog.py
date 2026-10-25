"""Normal builds, 50-ms resource measurements, and complete unchanged replay."""
import argparse,hashlib,json,subprocess,time
from pathlib import Path
import psutil
from core import HERE,BASE

PROJECT=BASE/'front-tools-catalog-20261024'
LAKE=BASE/'toolchain/lean-4.35.0-windows/bin/lake.exe'
PIN='3eca23c0a9fa6b153313655e6d51835406c2d06e'

def measured(argv,cwd,log):
    start=time.monotonic();peak=0;minfree=float('inf');reason=None
    with log.open('w',encoding='utf-8',newline='\n') as stream:
        process=subprocess.Popen(argv,cwd=cwd,stdout=stream,stderr=subprocess.STDOUT);owner=psutil.Process(process.pid)
        try:
            while process.poll() is None:
                try:children=[owner]+owner.children(recursive=True)
                except psutil.NoSuchProcess:children=[]
                rss=0
                for child in children:
                    try:rss+=child.memory_info().rss
                    except psutil.NoSuchProcess:pass
                free=psutil.virtual_memory().available;peak=max(peak,rss);minfree=min(minfree,free)
                if rss>8*1024**3:reason='owned RSS limit'
                elif free<2*1024**3:reason='minimum free RAM limit'
                elif time.monotonic()-start>300:reason='time limit'
                if reason:raise RuntimeError(reason)
                time.sleep(.05)
            if process.returncode:raise RuntimeError('Command failed: '+log.read_text(encoding='utf-8')[-3500:])
        finally:
            if process.poll() is None:
                try:children=owner.children(recursive=True)
                except psutil.NoSuchProcess:children=[]
                for child in reversed(children):
                    try:child.kill()
                    except psutil.NoSuchProcess:pass
                try:owner.kill()
                except psutil.NoSuchProcess:pass
                process.wait()
            info={'seconds':round(time.monotonic()-start,3),'peak_tree_rss_bytes':peak,
                  'minimum_free_bytes':minfree,'sampling_seconds':.05,'exit_code':process.returncode,
                  'guard_stop_reason':reason}
            log.with_suffix('.resources.json').write_text(json.dumps(info,indent=2)+'\n',encoding='utf-8',newline='\n')
    return info

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--resume',action='store_true')
    parser.add_argument('--project',type=Path,default=PROJECT);parser.add_argument('--lake',type=Path,default=LAKE)
    parser.add_argument('--output',type=Path,default=HERE/'front-tools-reviewed-evidence');args=parser.parse_args()
    project,lake=args.project.resolve(),args.lake.resolve()
    manifest=json.loads((HERE/'front-tools-reviewed-manifest.json').read_text(encoding='utf-8'))
    allowed={e['source'] for e in manifest['entries']}|{'Rule30PrizeKit.lean','build_all.sh','lean/README.md','lean/Ruliology.lean'}
    changed=set(subprocess.check_output(['git','diff',PIN,'--name-only'],cwd=project,text=True).splitlines())
    if not changed<=allowed:raise RuntimeError('Unexpected reference source changes: '+str(changed-allowed))
    for name,sha in manifest.get('metadata_sha256',{}).items():
        assert hashlib.sha256((project/name).read_bytes()).hexdigest()==sha
    checker=subprocess.check_output(['git','show',PIN+':Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    assert subprocess.check_output(['git','merge-base','HEAD',PIN],cwd=project,text=True).strip()==PIN
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True);done=[];dependencies={}
    for entry in manifest['entries']:
        module=entry['module'];source=project/entry['source'];raw=source.read_bytes()
        assert hashlib.sha256(raw).hexdigest()==entry['source_sha256']
        report=out/(module.rsplit('.',1)[-1]+'.json');keep=False
        if args.resume and report.exists():
            old=json.loads(report.read_text(encoding='utf-8'))
            obj=project/'lean/.lake/build/lib/lean'/(module.replace('.','/')+'.olean')
            keep=(old['source_sha256']==entry['source_sha256'] and old['dependency_sources']==dependencies
                  and old['kit_base']==PIN and old['checker_sha256']==hashlib.sha256(checker).hexdigest()
                  and old['check']['verdict']=='pass' and old['check']['replay']['ok'] and not old['check']['newAxioms']
                  and all(h['ok'] for h in old['check']['headlines']) and obj.exists())
        if keep:
            record=old;print({'module':module,'stage':'retained_exact_source_pass'},flush=True)
        else:
            print({'module':module,'stage':'normal_build'},flush=True)
            build=measured([str(lake),'build',module],project,out/(module+'.build.log'))
            print({'module':module,'stage':'kernel_replay','build_seconds':build['seconds'],
                   'build_peak_gb':round(build['peak_tree_rss_bytes']/1e9,3)},flush=True)
            argv=[str(lake),'env','lean','--run','Check.lean',module,'--claim','partial']
            for h in entry['headlines']:argv+=['--headline',h]
            log=out/(module+'.check.log');replay=measured(argv,project,log)
            checked=json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
            assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
            assert all(h['ok'] for h in checked['headlines']) and source.read_bytes()==raw
            record={'module':module,'source_sha256':entry['source_sha256'],'dependency_sources':dict(dependencies),
                    'kit_base':PIN,'checker_sha256':hashlib.sha256(checker).hexdigest(),
                    'build':build,'replay':replay,'check':checked,'full_problem_solved':False}
            report.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
            print({'module':module,'stage':'passed','constants':checked['replay']['constants']},flush=True)
        done.append(record);dependencies[module]=entry['source_sha256']
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    result={'verdict':'pass','entries':done,'full_problem_solved':False}
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'all_three_modules_passed':True,'constants':sum(r['check']['replay']['constants'] for r in done)},flush=True)

if __name__=='__main__':main()
