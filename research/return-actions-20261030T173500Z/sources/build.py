from pathlib import Path
import shutil,os,subprocess,time,json,sys
sys.stdout.reconfigure(encoding='utf-8')
R=Path(__file__).resolve().parent;P=R/'project';P.mkdir(exist_ok=True)
base=Path('D:/MWB/Rule30/group-cocycle-catalog-20261030/lean')
for name in ['Rule30Jen','Rule30Prize','Rule30Realization','Rule30FrozenRuler']:
    rel=Path('Ruliology/CellularAutomata')/(name+'.lean');dst=P/rel
    dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(base/rel,dst)
shutil.copyfile(R/'CanonicalDecoration.lean',P/'CanonicalDecoration.lean')
shutil.copyfile(R/'LeakDescent.lean',P/'LeakDescent.lean')
shutil.copyfile(R/'ReturnActions.lean',P/'ReturnActions.lean')
shutil.copyfile(R/'ReturnSections.lean',P/'ReturnSections.lean')
shutil.copyfile(R/'ReachabilityBarrier.lean',P/'ReachabilityBarrier.lean')
shutil.copyfile(R/'MaskDynamics.lean',P/'MaskDynamics.lean')
shutil.copyfile(base.parent/'Check.lean',P/'Check.lean')
lean=Path('D:/MWB/Rule30/toolchain/lean-4.35.0-windows/bin/lean.exe')
env=dict(os.environ,LEAN_PATH=str(P),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
start=time.monotonic()
for name in ['Ruliology/CellularAutomata/Rule30Jen','Ruliology/CellularAutomata/Rule30Prize',
             'Ruliology/CellularAutomata/Rule30Realization','Ruliology/CellularAutomata/Rule30FrozenRuler','CanonicalDecoration','LeakDescent','ReturnActions','ReturnSections','ReachabilityBarrier','MaskDynamics']:
    src=P/(name+'.lean')
    if name not in ['CanonicalDecoration','LeakDescent','ReturnActions','ReturnSections','ReachabilityBarrier','MaskDynamics'] and src.with_suffix('.olean').exists():continue
    with (R/(Path(name).name+'.log')).open('wb') as f:
        r=subprocess.run([str(lean),'-o',str(src.with_suffix('.olean')),str(src)],cwd=P,env=env,
                         stdout=f,stderr=subprocess.STDOUT,timeout=60)
    if r.returncode:
        print((R/(Path(name).name+'.log')).read_text(encoding='utf-8',errors='replace')[-5000:]);raise SystemExit(r.returncode)
print(json.dumps(dict(built=True,seconds=round(time.monotonic()-start,3))))
