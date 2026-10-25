"""Read-only exact-blob, algebraic-certificate and scope audit."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent;staged='--staged' in sys.argv
repo=next((p for p in root.parents if (p/'.git').exists()),None)
def read(p):
    if staged:
        assert repo
        return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
def obj(p):return json.loads(read(p))
m=obj(root/'artifacts.json');w=root/'work';s=obj(root/'summary.json')
assert set(m['files'])|{'artifacts.json'}=={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
for f,h in m['files'].items():
    p=(root/f).resolve();assert p.is_relative_to(root.resolve())
    assert hashlib.sha256(read(p)).hexdigest()==h,f
    if p.suffix=='.py':ast.parse(read(p),filename=f)
    if p.suffix=='.json':json.loads(read(p))
assert not any(s[k] for k in ['full_problem_solved','new_Lean_theorem','prize_api_submitted','uniform_observer_existence_proved','P1_proved'])
assert s['prior_hashes_unchanged']==600 and s['independently_checked_certificates']==2891
for name in s['guards_normal']:
    g=obj(w/'evidence'/(name+'.guard.json'))
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3
    assert g['minimum_system_available_bytes']>=2*1024**3
basic=obj(w/'source-observer.json');generic=obj(w/'observer-generic.json');stress=obj(w/'observer-stress.json')
assert basic['local_truth_table_controls']==128
canon=[r for r in basic['records'] if r['rule']==30]
control=[r for r in basic['records'] if r['rule']==210]
assert len(canon)==548 and all(r['certificate'] for r in canon)
assert len(control)==36 and sum(r['certificate'] is not None for r in control)==4
assert len(generic['records'])==2300 and all(r['certificate'] for r in generic['records'])
assert len(stress['records'])==33 and stress['stop']=='internal_time_budget'
assert all(r['certificate'] for r in stress['records'])
unique={(r['TA'],r['TB']) for r in canon+stress['records']}
assert len(unique)==571 and max(a for a,b in unique)==4096
adverse=obj(w/'observer-adversarial.json')
assert not adverse['unresolved'] and adverse['stop'] is None
assert sum(v for k,v in adverse['counts'].items() if k.startswith('exhaustive_'))==69904
assert sum(v for k,v in adverse['counts'].items() if k.startswith('structured_'))==11236
assert sum(1 for r in basic['records'] if r['certificate'])+2300+33+6==2891
audit=obj(w/'observer-independent-check.json')
assert audit['independent_backward_adjoint']=='PASS' and audit['certificates_checked']==2891
assert audit['deliberately_wrong_time_zero_certificates_rejected']==2891
assert not audit['Lean_verified'] and not audit['full_problem_solved']
for f,h in audit['sha256'].items():assert hashlib.sha256(read(w/f)).hexdigest()==h

def step(a,rule):
    return (a<<1)^(a|(a>>1)) if rule==30 else (a<<1)^((a>>1)&~a)

def certificate(r):
    cert=r['certificate'];assert cert
    W=r['TA'];N=cert['observed_through'];rule=r['rule']
    assert W>0 and N<=r['cap']
    origin=W+N+4;mask=(1<<(2*origin+1))-1
    if 'A_hex' in r:a,b=[int(r[k],16)<<(origin-W) for k in ('A_hex','B_hex')]
    else:
        a=b=1<<origin
        for _ in range(r['TA']):a=step(a,rule)&mask
        for _ in range(r['TB']):b=step(b,rule)&mask
    assert ((a^b)>>(origin-W))&1
    history=[];out=[]
    for t in range(N+1):
        history.append((a,b));out.append(((a^b)>>origin)&1)
        a,b=step(a,rule)&mask,step(b,rule)&mask
    times=cert['certificate_times'];assert times==sorted(set(times)) and times[-1]==N
    assert len(times)==cert['certificate_weight']
    chosen=set(times);q=0
    for t in range(N,-1,-1):
        if t in chosen:q^=1<<origin
        if t:
            a,b=history[t-1]
            cc=~(b>>1) if rule==30 else b>>1
            q=((q>>1)^(q&cc)^((q<<1)&~(a<<1)))&mask
    row=(q>>(origin-W))&((1<<(2*W+1))-1)
    assert row==1 and sum(out[t] for t in times)%2==1
    assert row^(1<<W)!=1

checked=0
for d in [basic,generic,stress]:
    for r in d['records']:
        if r['certificate']:certificate(r);checked+=1
smt=obj(w/'observer-smt.json');assert len(smt['records'])==9
assert sum(r['verdict']=='sat' for r in smt['records'])==6
assert sum(r['verdict']=='unknown' for r in smt['records'])==3
for r in smt['records']:
    if r['verdict']=='sat':
        W,N=r['W'],r['N'];offset=N+3;bits=2*W+1+2*offset;mask=(1<<bits)-1
        av,bv,hv=[int(r['witness'][k],16) for k in ('A_hex','B_hex','H_hex')]
        assert av&1 and not bv&1 and hv&1
        a,b,h=[v<<offset for v in (av,bv,hv)]
        for _ in range(N+1):
            assert not (h>>(offset+W)&1)
            a,b,h=step(a,30)&mask,step(b,30)&mask,((h<<1)^(h&~(b>>1))^((h>>1)&~a))&mask
        assert r['observer_at_N']['unresolved']
        certificate(dict(r['extended_observer'],**r['witness']));checked+=1
    else:assert r['reason_unknown']=='timeout'
assert checked==2891
hard=next(r for r in smt['records'] if r['W']==6 and r['N']==20)
assert hard['witness']=={'A_hex':'0x1d2b','B_hex':'0x978','H_hex':'0x503'}
assert hard['extended_observer']['certificate']['observed_through']==23
assert hard['extended_observer']['first_actual_center_disagreement']==0
profile=obj(w/'source-profiles.json')
assert profile['independent_difference_controls']==1089
assert profile['first_pair_counterexample']=={'r':3,'even_phase':4,'C_even':0,'C_odd':1}
assert not profile['parity_augmented_33_coordinate_aliases']
snapshot=obj(w/'refresh-result.json')
assert snapshot['count']==41 and snapshot['kit']['commit']==s['kit_commit']
assert not any(snapshot[k] for k in ['new_entries','changed_entries','removed_ids'])
for filename in ['REPORT.md','REPRODUCE.md']:
    for href in re.findall(r'\]\(([^)]+)\)',read(root/filename).decode('utf-8')):
        if '://' not in href:assert (root/href).exists(),href
print(json.dumps({'pass':True,'staged_blobs':staged,'hashes':len(m['files']),
                  'independent_certificate_checks':checked,'SMT_witnesses':6,
                  'Lean_verified':False,'full_problem_solved':False}))
