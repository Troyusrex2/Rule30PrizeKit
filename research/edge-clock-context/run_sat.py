from pathlib import Path
import subprocess,sys,json,time
import psutil
ROOT=Path(__file__).resolve().parent
def run(q,w,mode,expect=None):
    start=time.monotonic();peak=0;stopped=None
    log=ROOT/f'{mode}-q{q}-w{w}.log'
    with log.open('wb') as f:
        p=subprocess.Popen([sys.executable,'-X','utf8','-B',str(ROOT/'clock_sat.py'),str(q),str(w),mode],stdout=f,stderr=subprocess.STDOUT)
        owner=psutil.Process(p.pid)
        while p.poll() is None:
            try:
                rss=owner.memory_info().rss;peak=max(peak,rss)
                if time.monotonic()-start>8:stopped='UNKNOWN_WALL_LIMIT'
                elif rss>1024**3:stopped='UNKNOWN_MEMORY_LIMIT'
                if stopped:p.kill();p.wait();break
            except psutil.NoSuchProcess:break
            time.sleep(.05)
    p.wait()
    path=ROOT/f'{mode}-q{q}-w{w}/RESULT.json'
    if stopped:r={'clock':q,'width':w,'mode':mode,'status':stopped}
    else:
        assert p.returncode==0,log.read_text(encoding='utf-8')
        r=json.loads(path.read_text())
    r.update({'peak_rss_bytes':peak,'external_seconds':time.monotonic()-start})
    if expect:assert r['status']==expect,(q,w,mode,r['status'],expect)
    print(json.dumps({k:v for k,v in r.items() if k not in ['rows','stats']}),flush=True)
    return r
if __name__=='__main__':
    out=[]
    for q,w,mode,expected in [(4,4,'seed','SAT'),(2,4,'seed','UNSAT'),(4,3,'free','SAT'),(4,8,'drop','UNSAT'),(8,12,'drop','UNSAT')]:
        out.append(run(q,w,mode,expected))
    for q in [128,256]:
        for w in [24,32,40,48]:
            r=run(q,w,'drop');out.append(r)
            (ROOT/'SAT-RESULTS.json').write_text(json.dumps(out,indent=2)+'\n')
            if r['status']=='SAT':raise SystemExit('GENUINE COUNTEREXAMPLE: stop and audit')
    (ROOT/'SAT-RESULTS.json').write_text(json.dumps(out,indent=2)+'\n')
