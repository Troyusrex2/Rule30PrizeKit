from pathlib import Path
import hashlib,json,shutil
root=Path(__file__).resolve().parent;base=root.parent;deps={}
for phase,names in {
 'short-extension-root-review-20261026T1840':['CedarSafetySoundness','CedarSafetySemantics','CedarSafetyBridge'],
 'return8-bridge-review-20261026T1942':['CedarMarkerReturnTwo']}.items():
 for name in names:
  p=base/phase/(name+'.lean');r=json.loads((base/phase/'formal'/name/'report.json').read_text())
  assert r['checker']['verdict']=='pass' and r['checker']['replay']['ok']
  assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']
  deps[name]={'phase':phase,'source_sha256':r['source_sha256'],'compiled_sha256':r['compiled_sha256']}
  out=root/'dependencies';out.mkdir(exist_ok=True);shutil.copyfile(p,out/p.name)
  out=root/'dependency-receipts'/name;out.mkdir(parents=True,exist_ok=True)
  shutil.copyfile(base/phase/'formal'/name/'report.json',out/'report.json')
sources={p.stem:hashlib.sha256(p.read_bytes()).hexdigest() for p in root.glob('*.lean')}
(root/'sources.json').write_text(json.dumps({'sources':sources,'dependencies':deps},indent=2)+'\n')
shutil.copyfile(base/'safe-to-height-two-20261026T2042/guard.py',root/'guard.py')
replay=(base/'safe-to-height-two-20261026T2042/replay.py').read_text()
a=replay.index('heads=');b=replay.index('\nassert module in heads',a)
replay=replay[:a]+'''heads={'MarkerCarryAmbiguity':['no_short_view_marker_update','full_view_family_equal','future_carry_exposes_phase','no_full_view_update_on_nonreturn'],
       'MarkerCarryReconstruction':['view_and_last_two_injective','previous_eq'],
       'MarkerCarryProjectedCycle':['spurious_safe_projected_cycle','unique_phase_switch']}'''+replay[b:]
(root/'replay.py').write_text(replay)
print(json.dumps({'sources':sources,'dependencies':len(deps)}))
