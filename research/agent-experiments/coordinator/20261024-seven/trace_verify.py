"""Observe resource use of the existing guarded verifier; never relax its limits."""
import argparse,json,subprocess,sys,time
from pathlib import Path
import psutil
from core import HERE
from verification_context import add_reference_options

def main():
    parser=argparse.ArgumentParser();add_reference_options(parser)
    parser.add_argument('--module',required=True);parser.add_argument('--headlines',nargs='+',required=True)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True);start=time.monotonic();peak=0;minfree=float('inf')
    argv=[sys.executable,str(HERE/'verify_research_module.py'),'--module',args.module,
          '--headlines',*args.headlines,'--project',str(args.project),'--lake',str(args.lake),'--output',str(out)]
    with (out/'verifier.log').open('w',encoding='utf-8') as log:
        process=subprocess.Popen(argv,cwd=HERE,stdout=log,stderr=subprocess.STDOUT);owner=psutil.Process(process.pid)
        while process.poll() is None:
            try:children=[owner]+owner.children(recursive=True)
            except psutil.NoSuchProcess:children=[]
            rss=0
            for p in children:
                try:rss+=p.memory_info().rss
                except psutil.NoSuchProcess:pass
            peak=max(peak,rss);minfree=min(minfree,psutil.virtual_memory().available);time.sleep(.2)
    info={'module':args.module,'exit_code':process.returncode,'seconds':round(time.monotonic()-start,3),
          'peak_tree_rss_gib':round(peak/2**30,3),'minimum_free_gib':round(minfree/2**30,3),
          'existing_guard_unchanged':True}
    (out/'resources.json').write_text(json.dumps(info,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(info,flush=True)
    if process.returncode:print((out/'verifier.log').read_text(encoding='utf-8')[-1800:],flush=True)
    sys.exit(process.returncode)

if __name__=='__main__':main()
