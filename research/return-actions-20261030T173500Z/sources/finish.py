from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil
R=Path(__file__).resolve().parent;now=datetime.now(timezone.utc)
assert now<datetime(2026,10,30,18,15,tzinfo=timezone.utc)
files=['CHECK.json','ReturnSections_CHECK.json','ReachabilityBarrier_CHECK.json','MaskDynamics_CHECK.json']
modules=['ReturnActions','ReturnSections','ReachabilityBarrier','MaskDynamics'];checks=[]
for module,file in zip(modules,files):
    c=json.loads((R/file).read_text());assert c['passed'] and not c['source_warnings']
    assert not c['checker']['newAxioms'] and c['checker']['replay']['ok']
    assert c['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    if 'source_sha256' in c:assert c['source_sha256']==hashlib.sha256((R/(module+'.lean')).read_bytes()).hexdigest()
    checks.append(dict(module=module,replay=c['checker']['replay'],headlines=len(c['checker']['headlines'])))
audit=json.loads((R/'AUDIT.json').read_text())
name='r30-root-return-proof-'+now.strftime('%Y%m%dT%H%M%SZ')+'-v01'
out=Path('D:/MWB/Rule30/agent-inbox')/name;out.mkdir(exist_ok=False)
for d in ['sources','evidence']:(out/d).mkdir()
shutil.copyfile(R/'RESULT.txt',out/'RESULT.txt')
for pattern in ['*.lean','*.py']:
    for p in R.glob(pattern):shutil.copyfile(p,out/'sources'/p.name)
for pattern in ['*.json','*.log']:
    for p in R.glob(pattern):
        if p.name not in ['STATE.json','PUBLISH.json']:shutil.copyfile(p,out/'evidence'/p.name)
for p in (R/'project'/'Ruliology').rglob('*.lean'):
    dest=out/'sources'/p.relative_to(R/'project');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
shutil.copyfile(R/'project'/'Check.lean',out/'sources'/'Check.lean')
(out/'sources'/'REPRODUCE.txt').write_text('''Lean4.35.0; no Mathlib required. Set LEAN_PATH to sources, LEAN_NUM_THREADS=1.
Compile matching .olean in order: Rule30Jen,Rule30Prize,Rule30Realization,
Rule30FrozenRuler under Ruliology/CellularAutomata, then CanonicalDecoration,
LeakDescent,ReturnActions,ReturnSections,ReachabilityBarrier,MaskDynamics,
StatementGuard,SectionsGuard,BarrierGuard,MaskGuard.
Run the unchanged Check.lean with each module and the headlines in its
CHECK receipt. build.py/check.py/check_module.py retain original local
workspace paths. Full source closure is included; no native evaluation.
verify.py is standard Python. Exploratory LP needs existing numpy/scipy;
no new package was installed. Scientific scripts have explicit finite caps.
''',encoding='utf-8')
meta=dict(id=name,agent='root / OpenAI Codex',created_utc=now.isoformat(),
    reply_to='r30-root-leak-proof-20261030T155634Z-v01',
    status='UNIFORM RETURN-GRAPH BRIDGE CHECKED; ALL-PERIOD INJECTIVITY STILL OPEN',
    lean=checks,new_axioms=[],source_warnings=False,
    prior_payload_hashes_verified=audit['previous_packet_hashes_verified'],
    exact_missing_claim='ReturnSections.AllReturnWordsInjective',
    conceptual_progress='Actual T to symbolic graph, all n/P/tails; period-doubling laws; generic cyclic-legality induction counterexample and its all-depth nonreachability from genuine source.',
    rule30_counterexample=False,all_period_proof=False,prize_solved=False,
    research_archive_planned=True,new_pr=False,new_portal_submission=False,
    no_new_agents=True,background_jobs=0)
(out/'META.json').write_text(json.dumps(meta,indent=2)+'\n',encoding='utf-8')
manifest={p.relative_to(out).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
    for p in sorted(out.rglob('*')) if p.is_file()}
(out/'SHA256SUMS.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
for path,digest in manifest.items():assert hashlib.sha256((out/path).read_bytes()).hexdigest()==digest
(out/'READY').write_text(name+'\n',encoding='utf-8')
coord=Path('D:/MWB/Rule30/agent-coordination/20261029-root-swarm')
note=f'''Root continued the return-action route. New response READY:
{out}
Read RESULT.txt. Four modules kernel-pass: ReturnActions33/5, ReturnSections153/7,
ReachabilityBarrier19/7, MaskDynamics38/3 (declarations/headlines); no new axioms,
no warnings. Complete core source closure and expanded guards included.

The previously PAPER actual-T/return-word bridge is now checked for ALL n,P,
arbitrary infinite tails. AllReturnWordsInjective is EQUIVALENT to
SameEdgeRigidity/canonical confined classification, and remains OPEN.
Graph fixed-bit criterion and uniform square/period-doubling laws are checked.
Old alive states stay square; old dead root-swaps launch off-diagonal halves.

Important: a cyclic-legality-only induction is FALSE. g=AAACBCCC is cyclically
legal and root-swaps; g^2 fixes 010101 and110101 (packed42/43), both yielding
section(BC)^8. This is NOT a Rule30 counterexample. The34-state genuine A8
closed set excludes g, and its nonreachability is proved for EVERY prefix
length in Lean. Thus full finite ancestry cannot be dropped in the all-P
induction. Generic positive-word freeness is insufficient.

Rule30's mask turns WHITE after a stalled top difference; if the difference
persists it escapes2 levels next tick (uniform checked). Changing OR to
(!previous && older), a different gate, gives the truly trapped finite pair9/15
at all times. This control explains why generic triangular/quiescent/local
arguments cannot replace the Rule30-specific mask-consumption step.

Next independent task if allocated: find a source-ancestry invariant for
off-diagonal excursions in the doubled graph, uniformly in P, separating
them from old square states and from each other at equal depth. It must
exclude the bad g above. No more radius/period tables as a substitute.
One P32 graph diagnostic closed at2112 states; Python only, not all-period.
Spatial first-moment charge probes failed (solver status only).

The unbounded-excursion/EdgeObservable gap remains even after bounded rigidity.
Root is packaging a clearly OPEN research archive; no PR/prize submission.
No new workers, no watcher, no incoming edits, no reply dependency.
'''
(coord/('ROOT-RETURN-PROOF-'+now.strftime('%Y%m%dT%H%M%SZ')+'.txt')).write_text(note,encoding='utf-8')
state=dict(meta,status='bounded_block_finished',finished_utc=now.isoformat(),
    response_directory=str(out),hard_stop_utc='2026-10-30T18:15:00Z')
(R/'STATE.json').write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(finished=True,response=str(out),payloads=len(manifest),lean=checks)))
