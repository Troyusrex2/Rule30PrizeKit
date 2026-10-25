"""Independent scalar CA + coordinate-set replay of sparse certificates.

Does not import the producer, union-find, bit-plane evolution or variable IDs.
"""
from pathlib import Path
import json,hashlib,time
root=Path(__file__).resolve().parent
tick=time.monotonic()

def step(state,rule):
    if not state:return set()
    out=set()
    for p in range(min(state)-1,max(state)+2):
        l,c,r=p-1 in state,p in state,p+1 in state
        value=(l != (c or r)) if rule==30 else (l != (r and not c))
        if value:out.add(p)
    return out

def backgrounds(cert):
    U,V,N,rule=[cert[k] for k in ('U','V','through','rule')]
    pair=cert['initial_pair_hex']
    if pair is None:
        history=[{0}]
        for _ in range(U+N):history.append(step(history[-1],rule))
        return history[U:U+N+1],history[V:V+N+1]
    a,b=[{i-U for i in range(2*U+1) if int(v,16)>>i&1} for v in pair]
    aa,bb=[a],[b]
    for _ in range(N):aa.append(step(aa[-1],rule));bb.append(step(bb[-1],rule))
    return aa,bb

def replay(cert):
    U,V,N,rule=[cert[k] for k in ('U','V','through','rule')]
    assert U>V>=0 and N>=U and rule in (30,210)
    aa,bb=backgrounds(cert)
    assert min(aa[0]^bb[0])==-U
    assert all(-U<=p<=U for p in aa[0]|bb[0])
    actual_first=next((t for t in range(N+1) if (0 in aa[t])!=(0 in bb[t])),None)
    assert actual_first==cert['first_actual_center_disagreement']
    if not cert['edge_forced']:
        assert cert['rows']==[] and cert['observation_times']==[]
        return {'recovered':False,'actual_all_outputs_zero':actual_first is None}
    assert cert['rows'] and len({tuple(d) for d in cert['rows']})==len(cert['rows'])
    combined=set();observation_times=[];identities=0
    for kind,t,p in cert['rows']:
        assert isinstance(t,int) and isinstance(p,int) and 0<=t<=N
        if kind=='O':
            assert p==0;terms=[(t,0)];observation_times.append(t)
        elif kind in ('D','W'):
            assert t<N and abs(p)<=N-t-1
            a,b=aa[t],bb[t];delta=a^b
            if kind=='D':
                terms=[(t+1,p),(t,p-1)]
                cc=(p+1 not in b) if rule==30 else (p+1 in b)
                if cc:terms.append((t,p))
                if p not in a:terms.append((t,p+1))
            else:
                terms=[]
                if p+1 in delta:terms.append((t,p))
                if p in delta:terms.append((t,p+1))
            assert sum(((q in aa[s])!=(q in bb[s])) for s,q in terms)%2==0
            identities+=1
        else:raise AssertionError(kind)
        reduced=set()
        for s,q in terms:
            if not -U-s<=q<=U+s:
                assert q not in aa[s] and q not in bb[s]
                continue
            if (s,q) in reduced:reduced.remove((s,q))
            else:reduced.add((s,q))
        combined.symmetric_difference_update(reduced)
    assert combined=={(0,-U)}
    assert observation_times==cert['observation_times']
    assert sum(((0 in aa[t])!=(0 in bb[t])) for t in observation_times)%2==1
    assert len(cert['rows'])==cert['certificate_rows']
    return {'recovered':True,'identities':identities,'actual_all_outputs_zero':False}

def run():
    passed=[];rejected=[];negative=0;files={};records=[]
    for name in ['common-certificates.jsonl','deadline-certificates.jsonl']:
        path=root/name
        if path.exists():
            raw=path.read_bytes();files[name]=hashlib.sha256(raw).hexdigest()
            records += [json.loads(line) for line in raw.decode('utf-8').splitlines()]
    controls=json.loads((root/'common-controls.json').read_text(encoding='utf-8'))
    history=json.loads((root/'history-control.json').read_text(encoding='utf-8'))['record']
    controls += [history['sparse_N_equals_U']]
    if history.get('later_sparse_certificate'):controls.append(history['later_sparse_certificate'])
    inv=json.loads((root/'inverse-geometry-control.json').read_text(encoding='utf-8'))
    for collision in inv['collisions']:
        controls += [collision['N_equals_U_obstruction'],collision['later_sparse_certificate']]
    for i,cert in enumerate(records+controls):
        result=replay(cert);passed.append(result)
        if result['actual_all_outputs_zero']:negative+=1
        if cert['edge_forced']:
            broken=json.loads(json.dumps(cert))
            # Toggle time zero. It changes the combined row by the distinct
            # variable (0,0), so rejection happens before metadata checks.
            row=['O',0,0]
            if row in broken['rows']:broken['rows'].remove(row)
            else:broken['rows'].append(row)
            try:replay(broken)
            except AssertionError:rejected.append(i)
            else:raise AssertionError('Accepted a corrupted certificate')
    out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
         'canonical_certificates_passed':len(records),
         'canonical_unique_pairs':len({(r['U'],r['V']) for r in records}),
         'controls_passed':len(controls),'known_zero_output_witnesses':negative,
         'corrupt_certificates_rejected':len(rejected),
         'physical_local_identities_replayed':sum(r.get('identities',0) for r in passed),
         'certificate_files_sha256':files,'seconds':time.monotonic()-tick,
         'scope':'Independent exact scalar verification of finite row-combination certificates; no unbounded theorem and no Lean replay.'}
    (root/'common-independent-verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(out),flush=True)

if __name__=='__main__':run()
