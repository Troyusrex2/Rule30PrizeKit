from pathlib import Path
import subprocess,sys,time,json,psutil,os
ROOT=Path(__file__).resolve().parent;start=time.monotonic();peak=0;stop=None
assert psutil.virtual_memory().available>2*1024**3
with (ROOT/'run.log').open('wb') as log:
    child=subprocess.Popen([sys.executable,'-X','utf8','-B',str(ROOT/'probe.py')],stdout=log,stderr=subprocess.STDOUT,env=dict(os.environ,OMP_NUM_THREADS='1'));owner=psutil.Process(child.pid)
    while child.poll() is None:
        try:
            owned=[owner]+owner.children(recursive=True);rss=0
            for process in owned:
                try:rss+=process.memory_info().rss
                except psutil.NoSuchProcess:pass
            peak=max(peak,rss)
            if rss>1024**3:stop='owned_memory'
            elif time.monotonic()-start>60:stop='wall_time'
            elif psutil.virtual_memory().available<2*1024**3:stop='system_memory'
            if stop:
                for process in reversed(owned):
                    try:process.kill()
                    except psutil.NoSuchProcess:pass
                break
        except psutil.NoSuchProcess:break
        time.sleep(.05)
    child.wait()
r={'exit_code':child.returncode,'guard_stop':stop,'seconds':time.monotonic()-start,'peak_owned_tree_rss':peak,'limit_seconds':60,'limit_owned_tree_rss':1024**3}
(ROOT/'GUARD.json').write_bytes((json.dumps(r,indent=2)+'\n').encode());print(json.dumps(r));print((ROOT/'run.log').read_text(encoding='utf-8'))
raise SystemExit(child.returncode or (1 if stop else 0))
