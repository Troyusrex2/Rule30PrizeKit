from pathlib import Path
import ast,hashlib,json,subprocess,sys
root=Path(__file__).resolve().parent
repo=next(p for p in root.parents if (p/'.git').exists())
staged='--staged' in sys.argv
def read(p):
    if staged:return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
def obj(p):return json.loads(read(p))
m=obj(root/'artifacts.json');s=obj(root/'summary.json');w=root/'work'
assert set(m['files'])|{'artifacts.json'}=={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
for f,h in m['files'].items():
    raw=read(root/f);assert hashlib.sha256(raw).hexdigest()==h,f
    if f.endswith('.py'):ast.parse(raw,filename=f)
    if f.endswith('.json'):json.loads(raw)
assert s['prior_hashes_unchanged']==950
assert not any(s[k] for k in ['new_unbounded_theorem','full_problem_solved','full_notebook_fresh_verified',
                             'prize_api_submitted','new_long_running_waiter'])
r=obj(w/'trace-bridge-audit.json');c=r['check']
assert r['pass'] and r['existing_theorem_reaudited'] and not r['EdgeObservable_proved']
assert r['kit_commit']==s['kit_commit'] and r['checker_unchanged']
assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert c['verdict']=='pass' and c['replay']=={'constants':14,'ok':True} and not c['newAxioms']
assert len(c['headlines'])==3 and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
assert r['source_sha256']==hashlib.sha256(read(w/'Rule30TraceEdge.lean')).hexdigest()
p=obj(w/'periodic-tail-trace.json')
assert p['parameterized_starts']==32004 and p['horizon']==128 and not p['full_horizon_collisions']
assert p['scalar_and_doubled_horizon_controls']==152 and p['longest_different_edge_common_prefix']==23
q=obj(w/'unrestricted-right-probe.json')
assert [v['verdict'] for v in q['controls']]==['sat','unsat']
assert q['probe']['edge_depths']==[5,4] and q['probe']['observations']==32 and q['probe']['verdict']=='unsat'
assert not q['unbounded_edge_observability_proved']
for stage in ['build','fresh']:
    t=obj(w/'essay'/('workflow-canary-'+stage+'.json'))
    assert t['pass'] and t['sourceIconized'] and t['inputCells']==3
    assert t['completeKernelReplayDeclarations']==1 and not t['prizeNotebookValidated']
a=obj(w/'essay/workflow-canary-build.json');b=obj(w/'essay/workflow-canary-fresh.json')
assert a['notebookSHA256']==b['notebookSHA256']==hashlib.sha256(read(w/'essay/workflow-canary.nb')).hexdigest()
assert b['sourceRoundTrip'] and b['separateFreshProcess']
preview=obj(w/'essay/preview-packaging.json');src=read(w/'essay/Rule30Submission.lean')
assert preview['packagingPass'] and preview['sourceRoundTrip'] and preview['sourceIconized']
assert preview['inputCells']==7 and not preview['proofCellsExecuted'] and not preview['freshNotebookVerified']
assert preview['sourceSHA256']==hashlib.sha256(src).hexdigest()=='79e050af6000b66bc0c5a47f74d714e2e36b05ad85ad3783925e2e8f4363473d'
assert preview['notebookSHA256']==hashlib.sha256(read(w/'essay/product-parity-preview-unevaluated.nb')).hexdigest()
old=root.parent/'20261025-product-parity/work/essay-draft/evidence/Rule30Submission/report.json'
oldcheck=obj(old)
assert oldcheck['source_sha256']==preview['sourceSHA256'] and oldcheck['check']['replay']=={'constants':207,'ok':True}
assert oldcheck['check']['verdict']=='pass' and not oldcheck['check']['newAxioms']
gate=obj(w/'essay/build-launch-state.json')
assert gate['state']=='not_started_insufficient_memory' and gate['required_available_bytes']==10500000000
assert gate['available_bytes']<gate['required_available_bytes']
oldwait=obj(w/'old-memory-wait-status.json')
assert oldwait['state']=='wait_timed_out' and not oldwait['fresh_notebook_verified']
for job in s['passed_guarded_jobs']:
    g=obj(w/'evidence'/(job+'.guard.json'))
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
g=obj(w/'evidence/build_product_essay.guard.json')
assert g['exit_code']==3 and g['guard_stop'] is None
print(json.dumps({'pass':True,'staged_blobs':staged,'selected_hashes':len(m['files']),
                  'existing_bridge_constants':14,'full_notebook_fresh_verified':False,
                  'new_unbounded_theorem':False,'full_problem_solved':False}))
