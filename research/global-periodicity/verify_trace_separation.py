"""Build and replay every split separation certificate with bounded resources."""
import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
import psutil

HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[1]
PREFIX='Ruliology.CellularAutomata.'
ENGINE=PREFIX+'Rule30TraceSeparationResearch'
ROOT=PREFIX+'Rule30TraceSeparationThreeResearch'


def execute(argv,cwd,log):
    process=subprocess.Popen(argv,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                             encoding='utf-8',errors='replace')
    task=psutil.Process(process.pid)
    started=time.monotonic()
    try:
        while True:
            try:
                output,_=process.communicate(timeout=0.5)
                break
            except subprocess.TimeoutExpired:
                try: owned=[task]+task.children(recursive=True)
                except psutil.NoSuchProcess: owned=[]
                rss=0
                for p in owned:
                    try: rss+=p.memory_info().rss
                    except psutil.NoSuchProcess: pass
                if rss>4*1024**3 or psutil.virtual_memory().available<2*1024**3 or time.monotonic()-started>300:
                    for p in reversed(owned):
                        try: p.kill()
                        except psutil.NoSuchProcess: pass
                    raise RuntimeError('Owned verification job exceeded its memory/time budget; no pass claimed')
        log.write_text(output,encoding='utf-8',newline='\n')
        if process.returncode:
            raise RuntimeError(output[-2200:])
        return output
    finally:
        if process.poll() is None:
            for p in reversed(task.children(recursive=True)):
                try: p.kill()
                except psutil.NoSuchProcess: pass
            process.kill()
            process.communicate()


def verify_module(lake,project,evidence,module,headline):
    stem=module.removeprefix(PREFIX)
    started=time.monotonic()
    execute([lake,'build',module],project,evidence/(stem+'.build.log'))
    raw=execute([lake,'env','lean','--run','Check.lean',module,'--claim','partial','--headline',headline],
                project,evidence/(stem+'.check.log'))
    data=json.loads([s for s in raw.splitlines() if s.startswith('{')][-1])
    assert data['verdict']=='pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    (evidence/(stem+'.check.json')).write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
    result={'module':module,'verdict':'pass','constants':data['replay']['constants'],
            'seconds':round(time.monotonic()-started,3)}
    print(json.dumps(result),flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake',default='lake')
    parser.add_argument('--pinned-project',type=Path)
    parser.add_argument('--workers',type=int,default=2)
    args=parser.parse_args()
    project=args.pinned_project.resolve() if args.pinned_project else PROJECT
    tag='pinned' if args.pinned_project else 'catalog'
    evidence=HERE/'separation-evidence'/tag
    evidence.mkdir(parents=True,exist_ok=True)
    manifest=json.loads((HERE/'separation-chunk-manifest.json').read_text(encoding='utf-8'))
    rels=[Path('lean/Ruliology/CellularAutomata')/(n+'.lean') for n in [
          'Rule30TraceEdgeResearch','Rule30TraceSeparationResearch','Rule30TraceSeparationThreeResearch']]
    rels += [Path(x['relative_path']) for x in manifest['modules']]
    if args.pinned_project:
        for relative in rels:
            source=(PROJECT/relative).read_text(encoding='utf-8')
            adapted=source.removeprefix('module\n').replace('public import ','import ')
            adapted=adapted.replace('@[expose] public section','')
            target=project/relative
            if target.exists() and target.read_text(encoding='utf-8')!=adapted:
                raise RuntimeError('Refusing to overwrite different research source in the pinned worktree')
            target.write_text(adapted,encoding='utf-8',newline='\n')
    report={'full_problem_claim':False,'edge_observable_proved':False,
            'right_halves_unrestricted':True,'bounded_results_unconditional':True,
            'source_sha256':{r.as_posix():hashlib.sha256((project/r).read_bytes()).hexdigest() for r in rels},
            'modules':[]}
    def record(result):
        report['modules'].append(result)
        (HERE/f'separation-{tag}-verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    record(verify_module(args.lake,project,evidence,ENGINE,ENGINE+'.separate_minus_one_minus_two'))
    for chunk_stage in [True,False]:
        jobs=[]
        for item in manifest['modules']:
            module=item['module']
            match=re.search(r'M(\d)Chunk(\d+)$',module)
            if bool(match)!=chunk_stage: continue
            if match:
                m,index=map(int,match.groups())
                headline=PREFIX+f'Rule30TraceSeparationData.m{m}_leaf_{index*manifest["per_module"]}'
            else:
                m=int(module[-1])
                headline=PREFIX+f'Rule30TraceSeparationData.m{m}_full_mask'
            jobs.append((module,headline))
        with ThreadPoolExecutor(max_workers=args.workers) as executor:
            futures=[executor.submit(verify_module,args.lake,project,evidence,*job) for job in jobs]
            for future in as_completed(futures): record(future.result())
    record(verify_module(args.lake,project,evidence,ROOT,ROOT+'.separate_minus_two_minus_three'))
    report['verdict']='pass'
    report['all_modules_replayed']=True
    (HERE/f'separation-{tag}-verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'verdict':'pass','module_count':len(report['modules']),'project':tag}),flush=True)


if __name__=='__main__': main()
