"""Exact finite common-gauge certificates with row-combination provenance.

The weighted union-find is only a producer. verify_common.py reconstructs and
checks the selected rows independently, without trusting this elimination.
"""
from pathlib import Path
import hashlib, json, sys, time
root=Path(__file__).resolve().parent

def advance(a,rule):
    if rule==30:return (a<<1)^(a|(a>>1))
    if rule==210:return (a<<1)^((a>>1)&~a)
    raise ValueError(rule)

def build(U,V,N,rule=30,initial_pair=None):
    assert U>V>=0 and N>=U and rule in (30,210)
    origin=U+N+4;mask=(1<<(2*origin+1))-1
    if initial_pair is None:
        a=b=1<<origin
        for _ in range(U):a=advance(a,rule)&mask
        for _ in range(V):b=advance(b,rule)&mask
    else:
        assert initial_pair[0]&1 and not initial_pair[1]&1
        assert all(0<=v<1<<(2*U+1) for v in initial_pair)
        a,b=[v<<(origin-U) for v in initial_pair]
    ids={};coordinates=[None];rows=[];descriptors=[];actual=[0]
    controls=0;center_trace=[]
    def var(t,p,delta):
        if not -U-t<=p<=U+t:return None
        key=t,p
        if key not in ids:
            ids[key]=len(coordinates);coordinates.append(key)
            actual.append((delta>>(origin+p))&1)
        return ids[key]
    def add(terms,desc,physical):
        nonlocal controls
        row=set()
        for x in terms:
            if x is None:continue
            if x in row:row.remove(x)
            else:row.add(x)
        if physical:
            assert sum(actual[x] for x in row)%2==0
            controls+=1
        if row:rows.append(tuple(sorted(row)));descriptors.append(desc)
    for t in range(N+1):
        delta=a^b;radius=N-t
        center_trace.append((delta>>origin)&1)
        add([var(t,0,delta)],('O',t,0),False)
        if t==N:break
        an,bn=advance(a,rule)&mask,advance(b,rule)&mask
        for p in range(-radius+1,radius):
            cc=((b>>(origin+p+1))&1)^(1 if rule==30 else 0)
            rc=((a>>(origin+p))&1)^1
            terms=[var(t+1,p,an^bn),var(t,p-1,delta)]
            if cc:terms.append(var(t,p,delta))
            if rc:terms.append(var(t,p+1,delta))
            add(terms,('D',t,p),True)
            terms=[]
            if (delta>>(origin+p+1))&1:terms.append(var(t,p,delta))
            if (delta>>(origin+p))&1:terms.append(var(t,p+1,delta))
            add(terms,('W',t,p),True)
        a,b=an,bn
    return coordinates,ids,rows,descriptors,controls,center_trace

def certify(U,V,N,rule=30,initial_pair=None):
    coordinates,ids,rows,descs,controls,trace=build(U,V,N,rule,initial_pair)
    count=len(coordinates);parent=list(range(count));size=[1]*count;proof=[0]*count
    # Node 0 is permanently the known zero. For all i, proof[i] certifies
    # X_i + X_parent[i] = XOR of the original equation rows in proof[i].
    def find(x):
        if parent[x]!=x:
            old=parent[x];r,w=find(old);proof[x]^=w;parent[x]=r
        return parent[x],proof[x]
    rounds=0;merge_kinds={'O':0,'D':0,'W':0}
    while True:
        rounds+=1;changed=False
        for j,row in enumerate(rows):
            reduced=set();comb=1<<j
            for x in row:
                r,w=find(x);comb^=w
                if not r:continue
                if r in reduced:reduced.remove(r)
                else:reduced.add(r)
            if len(reduced)==1:
                r=next(iter(reduced));parent[r]=0;proof[r]=comb
            elif len(reduced)==2:
                r,s=sorted(reduced)
                if size[r]>size[s]:r,s=s,r
                parent[r]=s;proof[r]=comb;size[s]+=size[r]
            else:continue
            merge_kinds[descs[j][0]]+=1;changed=True
        if not changed:break
    target=ids[(0,-U)];r,comb=find(target)
    selected=[]
    if r==0:
        check=set()
        for j,row in enumerate(rows):
            if comb>>j&1:
                check.symmetric_difference_update(row);selected.append(list(descs[j]))
        assert check=={target}
        observations=[d[1] for d in selected if d[0]=='O']
        assert sum(trace[t] for t in observations)%2==1
    else:observations=[]
    cert={'U':U,'V':V,'rule':rule,'through':N,
        'initial_pair_hex':[hex(x) for x in initial_pair] if initial_pair else None,
        'edge_forced':r==0,'rows':selected,'observation_times':observations,
        'first_actual_center_disagreement':next((t for t,x in enumerate(trace) if x),None),
        'variables':count-1,'equations':len(rows),'rounds':rounds,
        'merges_by_kind':merge_kinds,'identity_controls':controls,
        'certificate_rows':len(selected),
        'maximum_certificate_time':max((d[1]+(d[0]=='D') for d in selected),default=None)}
    return cert

def run():
    tick=time.monotonic();old=json.loads((root/'joint-gauge.json').read_text(encoding='utf-8'))
    cases=[(r['U'],r['V'],r['through']) for r in old['records'] if r['joint_gauges']]
    output=root/'common-certificates.jsonl';total=0;max_rows=0;canonical_failures=[]
    with output.open('w',encoding='utf-8') as stream:
        for U,V,N in cases:
            assert time.monotonic()-tick<210
            cert=certify(U,V,N)
            if not cert['edge_forced']:canonical_failures.append([U,V,N])
            stream.write(json.dumps(cert,separators=(',',':'))+'\n')
            total+=1;max_rows=max(max_rows,cert['certificate_rows'])
    controls=[]
    for U,V in [(2,1),(3,1),(4,2),(8,4),(16,8)]:
        cert=certify(U,V,4*U+32,210)
        # A physical nonzero source with all outputs zero must forbid a
        # separating certificate. The independent verifier also checks this.
        if cert['first_actual_center_disagreement'] is None:assert not cert['edge_forced']
        controls.append(cert)
    (root/'common-controls.json').write_text(json.dumps(controls,indent=2)+'\n',encoding='utf-8')
    summary={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
        'canonical_cases':total,'canonical_failures':canonical_failures,
        'maximum_certificate_rows':max_rows,'seconds':time.monotonic()-tick,
        'certificate_sha256':hashlib.sha256(output.read_bytes()).hexdigest(),
        'controls':[{'U':c['U'],'V':c['V'],'rule':c['rule'],
           'edge_forced':c['edge_forced'],'first_actual_center_disagreement':c['first_actual_center_disagreement']}
           for c in controls]}
    (root/'common-certificate-summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(summary),flush=True)

if __name__=='__main__':run()
