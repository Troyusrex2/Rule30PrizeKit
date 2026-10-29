"""Fresh core-Lean replay of the bounded pair-factor barrier. No downloads."""
from pathlib import Path
import argparse,os,shutil,subprocess,json,hashlib,time
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--lean',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();lean=args.lean.resolve();out=args.out.resolve();out.mkdir(parents=True,exist_ok=False)
    for rel,h in json.loads((HERE/'PAIR-INPUT-HASHES.json').read_text()).items():assert sha(HERE/rel)==h,rel
    src=out/'sources';src.mkdir();logs=out/'logs';logs.mkdir()
    modules=['Ruliology.CellularAutomata.Rule30Jen','Ruliology.CellularAutomata.Rule30Prize','PairFactorBarrier']
    for name in modules:
        rel=Path(name.replace('.','/')+'.lean');dest=src/rel;dest.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(HERE/'sources'/rel,dest)
    shutil.copy2(HERE/'Check.lean',src/'Check.lean')
    env=dict(os.environ,LEAN_PATH=str(src),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
    version=subprocess.check_output([str(lean),'--version'],env=env,text=True).strip();assert 'version 4.35.0,' in version
    def run(args,log):
        with (logs/log).open('wb') as f:r=subprocess.run([str(lean)]+args,cwd=src,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=45)
        if r.returncode:
            print((logs/log).read_text(encoding='utf-8',errors='replace')[-3000:]);r.check_returncode()
    start=time.monotonic()
    for name in modules:
        rel=name.replace('.','/');run(['-o',rel+'.olean',rel+'.lean'],name+'.build.log')
        assert 'warning:' not in (logs/(name+'.build.log')).read_text()
    run(['--run','Check.lean','PairFactorBarrier','--claim','partial','--headline','PairFactorBarrier.no_nonconstant_pair_factor'],'PairFactorBarrier.check.log')
    result=json.loads(next(x for x in reversed((logs/'PairFactorBarrier.check.log').read_text().splitlines()) if x.startswith('{')))
    assert result['verdict']=='pass' and result['replay']['ok'] and not result['newAxioms']
    record={'passed':True,'lean_version':version,'fresh_official_modules':2,'fresh_owned_modules':1,
      'reused_owned_objects':False,'mathlib':False,'constants':result['replay']['constants'],
      'headlines':1,'newAxioms':result['newAxioms'],'scope':'Fixed block size2/time2/binary radius1 factor maps only',
      'prize_solution':False,'checker_sha256':sha(HERE/'Check.lean'),'seconds':time.monotonic()-start}
    (out/'RESULT.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(record,indent=2))
if __name__=='__main__':main()
