from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
r=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=r,text=True).strip())
prefix=r.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if args.staged else (r/n).read_bytes()
def data(n):return json.loads(read(n))
m=data('artifacts.json')['files']
for n,h in m.items():assert hashlib.sha256(read(n)).hexdigest()==h,n
pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
checker='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(subprocess.check_output(['git','show',pin+':Check.lean'],cwd=repo)).hexdigest()==checker
assert data('work/environment.json')['kit']['commit']==pin
meta=data('work/pr31-source.json')
assert meta['head_commit']=='16250824c5e80964495ca5ba6bb82fa69394a35a'
assert meta['full_local_kernel_replay_passed'] and not meta['pending_full_replay']
for case,filename,decls in [('data','WhiteEndNineChecks.lean',38),('main','Rule30WhiteEndNine.lean',29)]:
    f=data('work/formal/pr31-'+case+'/report.json');src=read('work/'+filename);sha=hashlib.sha256(src).hexdigest()
    assert sha in meta['files'].values() and f['source_sha256']==sha
    original_path=next(n for n,h in meta['files'].items() if h==sha)
    assert src==subprocess.check_output(['git','show',meta['head_commit']+':'+original_path],cwd=repo)
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',src,re.M)
    assert f['passed'] and f['kit_commit']==pin and f['checker_unchanged'] and f['checker_sha256']==checker
    c=f['check'];assert c['verdict']=='pass' and c['replay']=={'constants':decls,'ok':True} and not c['newAxioms']
    assert all(x['ok'] and x['typeMatches'] for x in c['headlines'])
    assert not f['external_work_claimed_as_ours'] and not f['full_problem_solved']
    g=data('work/evidence/pr31-'+case+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None
seed=data('work/seed-ancestry-check.json')
assert all(not x['first_older_extension_exists'] for x in seed['reports'])
assert seed['global_boundary_necessity_not_established_by_these_seed_collisions']
assert seed['seed_source_sha256']==hashlib.sha256(read('work/seed-original-collision.json')).hexdigest()
strip=data('work/strip-ancestry-probe.json')
assert strip['both_h_phases_checked'] and strip['older_periods_not_forced_to_divide_P']
assert strip['candidate_pairs']==576 and [x['surviving_pairs'] for x in strip['reports']]==[576,320,240,112]
assert strip['reports'][-1]['mode_collision'] is None
sat=data('work/mode-strip-sat.json')
assert [x['status'] for x in sat['reports']]==['sat','unsat','sat','sat','sat','sat']
for x in sat['reports']:
    if x['status']!='sat':continue
    assert x['literal_audit_passed'] and not x['white_boundary']
    seen=[];T=x['cyclic_time_clock'];P=x['P'];R=x['R']
    for witness in x['witnesses']:
        values=witness['profiles_oldest_to_newest'];rows=[[v>>t&1 for v in values] for t in range(T)]
        for t,row in enumerate(rows):
            for j in range(2,len(row)):
                assert rows[(t+1)%T][j]==((30>>(4*row[j]+2*row[j-1]+row[j-2]))&1)
            assert rows[(t+P)%T][-2]==1-row[-2]
            assert rows[(t+R)%T][-3]==1-row[-3]
            assert rows[(t+R)%T][-4]==row[-4]
        q=[rows[(t+P)%T][-1]^rows[t][-1] for t in range(T)]
        rho=[(rows[(t+P)%T][-1]|rows[(t+P)%T][-2])^(rows[t][-1]|rows[t][-2]) for t in range(T)]
        S=[1^rho[(t+1)%T]^rho[t] for t in range(T)]
        assert q==witness['q'] and S==witness['S'];seen.append((q,S))
    assert seen[0][0][0]!=seen[1][0][0] and seen[0][1]==seen[1][1]
boundary=data('work/boundary-sat-probe.json')
assert all(x['status']=='unknown' and 'timeout' in x['reason_unknown'] for x in boundary['reports'])
cubic=data('work/mode-cubic-probe.json')['reports'][-1]
assert cubic['clock']==64 and cubic['mode_classes']==41792 and cubic['cubic_rank']==41600
assert not cubic['target_recovered'] and cubic['negative_witness_rows']==20726
a=data('work/compact-cubic-independent-audit.json')
assert a['passed'] and a['all_cubic_moments_checked']==43745 and a['target_xor']==1
assert a['witness_sha256']==hashlib.sha256(read('work/mode-cubic-compact-witness.json')).hexdigest()
safe=data('work/safe-stress-orbits.json');last=safe['reports'][-1]
assert last['width']==32 and last['all_words']==2**32 and last['safe_words']==339
assert last['complete_orbits']==773950 and last['maximum_period']==131072
assert last['non_period_eight_counterexample'] is None and not safe['uniform_unary_rigidity_proved']
ind=data('work/safe-language-independent-audit.json');assert ind['passed'] and not ind['uniform_classification_proved']
assert ind['width32_safe_words']==339 and ind['all_words_through_12_checked_by_literal_rule_table']
assert data('work/safe-language-rank.json')['status']=='unsat'
assert all(x['status']=='unsat' for x in data('work/safe-discount-rank.json')['reports'])
activity=data('work/activity-feed-summary.json');feed=data('work/activity-public-feed.json')
assert activity['raw_sha256']==hashlib.sha256(read('work/activity-public-feed.json')).hexdigest()
assert activity['public_entries']==len(feed['entries'])==41
assert activity['currently_listed_troy_entries']==3 and activity['other_entries']==38
assert activity['troy_lean_verified']==activity['troy_human_verified']==activity['troy_kit_contributions']==3
for file in [n for n in m if n.startswith('work/evidence/') and n.endswith('.guard.json')]:
    g=data(file);assert g['exit_code']==0 and g['guard_stop'] is None,file
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
    assert g['minimum_system_available_bytes']>=2*1024**3
s=data('summary.json');assert s['new_our_Lean_theorems']==0 and s['external_pr31_replayed_constants']==67
for n in ['mode_observer_refuted','uniform_safe_trace_classification_proved','physical_center_bridge_proved',
          'full_problem_solved','new_pull_request','new_prize_submission','our_work_Wolfram_backend_verified']:assert not s[n]
count=archives=0
for old in r.parent.glob('*/artifacts.json'):
    if old.parent.name in {'20261024-seven','20261025-round2','20261025-round2-review',r.name}:continue
    files=json.loads(old.read_bytes())['files']
    for n,h in files.items():assert hashlib.sha256((old.parent/n).read_bytes()).hexdigest()==h,(old.parent.name,n)
    count+=len(files);archives+=1
assert (count,archives)==(3081,37)
for n in m:assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(m),
  'external_replayed_constants':67,'new_our_Lean_theorems':0,'prior_hashes_unchanged':count,'full_problem_solved':False}))
