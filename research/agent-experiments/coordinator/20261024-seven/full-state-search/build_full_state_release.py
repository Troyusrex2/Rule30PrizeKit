"""Copy only explicitly selected completed mathematical research artifacts."""
import hashlib,json,shutil
from pathlib import Path
from core import HERE,REPO

DEST=REPO/'research/agent-experiments/coordinator/20261024-seven'
ROOT=DEST/'full-state-search'

def main():
 selected=set(json.loads((HERE/'full-state-source-closure.json').read_text()))
 selected.update(['full-state-source-closure.json','folded_bounded_geometric_rank.py','prepare_bounded_geometric_rank.py','retry_signed_geometric.py','folded_signed_geometric_ds.py','audit_ordered_reader_v3.py','validate_ordered_reader_v2.py','guard_folded_row_reader.py','ordered-reader-v2/train_ordered_rank_reader.py'])
 selected.update('''universal-full-row-controls.json universal-full-row-physical-controls.json universal-full-row-rank.json
 universal-folded-row-controls.json universal-folded-row-physical-controls.json universal-folded-row-rank.json
 folded-two-state-readers.json folded-prefix-peak-controls.json folded-prefix-peak-physical-controls.json
 universal-folded-prefix-peak.json universal-folded-prefix-peak-lagged.json folded-prefix-peak-lagged-controls.json
 folded-prefix-peak-lagged-physical-controls.json folded-peak-game-controls.json folded-peak-game.json
 folded-badclass-controls.json folded-badclass-nonnegative-sum.json folded-badclass-prefix-peak.json
 folded-geometric-controls.json folded-geometric-badclass.json folded-prefix-obstruction-cnf.json
 bad-language-strip-controls.json bad-language-strip.json geometric-gauge-controls.json
 folded-signed-geometric-controls.json folded-signed-geometric.json folded-signed-geometric-ds-retry.json
 folded-bounded-geometric-controls.json folded-bounded-geometric.json'''.split())
 for folder in ['folded-row-reader','folded-row-teacher','folded-peak-policy']:
  for p in (HERE/folder).rglob('*'):
   if p.is_file() and '_cache' not in p.parts and '__pycache__' not in p.parts:selected.add(p.relative_to(HERE).as_posix())
 selected.update('''external/d1bcba/Rule30Submission.lean external/d1bcba/provenance.json
 external/d1bcba/ExternalFinitePsiBadClassV2AuditResearch.lean external/d1bcba/badclass-extract-provenance-v2.json
 external/d1bcba/audit_remote_v5.py external/d1bcba/sources-v5.json external/d1bcba/OWNER.txt
 external/d1bcba/badclass-evidence-g913-v2/report.json external/d1bcba/badclass-evidence-g913-v2/build.log
 external/d1bcba/badclass-evidence-g913-v2/check.log external/d1bcba/badclass-evidence-g913-v2/build.resources.json
 external/d1bcba/badclass-evidence-g913-v2/check.resources.json'''.split())
 selected.add('build_full_state_release.py')
 ROOT.mkdir(exist_ok=True)
 for name in sorted(selected):
  src=HERE/name;target=ROOT/name;assert src.is_file() and src.resolve().is_relative_to(HERE.resolve()),name
  target.parent.mkdir(parents=True,exist_ok=True)
  if target.exists():assert target.read_bytes()==src.read_bytes(),('Refuse to replace released artifact',name)
  else:shutil.copyfile(src,target)
 (ROOT/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof\n*.npz binary\n*.pt binary\n',encoding='utf-8',newline='\n')
 (ROOT/'.gitignore').write_text('!folded-row-reader/actual-bothzero-ordered.npz\n!folded-row-reader/results/relu-reader-weights.pt\n!folded-row-teacher/actual-bothzero-ordered.npz\n!folded-row-teacher/results/relu-reader-weights.pt\n',encoding='utf-8',newline='\n')
 files={p.relative_to(DEST).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in ROOT.rglob('*') if p.is_file()}
 manifest={'kit_commit':'3eca23c0a9fa6b153313655e6d51835406c2d06e','checker_sha256':'b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905','scope':'complete finite spatial configurations; exact transducer controls, numerical searches, failed neural ranks, independently replayed external reduction','new_prize_result':False,'full_problem_solved':False,'files':dict(sorted(files.items()))}
 (DEST/'full-state-artifacts.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
 print({'files':len(files),'bytes':sum((DEST/n).stat().st_size for n in files),'destination':str(ROOT)},flush=True)
if __name__=='__main__':main()
