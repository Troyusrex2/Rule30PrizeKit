"""Exact cancellation-aware ancestry, finite controls, and liveness falsification.

Coordinates are physical: f(l,c,r)=l XOR(c OR r). No crops, periodic
boundaries, neural scores, numerical tolerances or unverified proof claims.
"""
import hashlib, itertools, json, random, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def rule(l,c,r, number=30):
    return (number >> (4*l+2*c+r)) & 1

def step(row, number=30):
    if not row:
        return set()
    assert rule(0,0,0,number) == 0
    return {x for x in range(min(row)-1, max(row)+2)
            if rule(int(x-1 in row), int(x in row), int(x+1 in row),number)}

def phi(a):
    return a ^ ((a<<1)|(a<<2))

def decode(a, frame):
    return {frame-i for i in range(a.bit_length()) if (a>>i)&1}

def active(a,b,x,gauge):
    """Active parent positions in either exact OR-difference factorization."""
    d=a^b
    if gauge == 0:
        weights=[1, int(x+1 not in a), int(x not in b)]
    else:
        weights=[1, int(x+1 not in b), int(x not in a)]
    return [p for p,w in zip([x-1,x,x+1],weights) if w and p in d]

def normalization(a,b,x):
    d=a^b
    out=rule(int(x-1 in a),int(x in a),int(x+1 in a)) ^ rule(int(x-1 in b),int(x in b),int(x+1 in b))
    # Exact same switch as CedarAncestry.weights, including even-output nodes.
    # The latter may acquire a pair rather than zero contributions; both cancel.
    gauge=int(x-1 not in d and x in d and x+1 in d and x+1 in a)
    wanted=None
    if out:
        wanted=min(p for p in (x-1,x,x+1) if p in d)
    incoming=active(a,b,x,gauge)
    assert len(incoming)%2==out
    if out:
        assert wanted in incoming
        remainder=[p for p in incoming if p!=wanted]
    else:
        remainder=incoming[:]
    assert len(remainder) in (0,2)
    return wanted,gauge,incoming,remainder

def local_controls():
    cases=[]
    switches=0
    for bits in itertools.product((0,1),repeat=6):
        a={x for x,v in zip((-1,0,1),bits[:3]) if v}
        b={x for x,v in zip((-1,0,1),bits[3:]) if v}
        parent,gauge,inc,pair=normalization(a,b,0)
        out=rule(*bits[:3])^rule(*bits[3:])
        for g in (0,1): assert len(active(a,b,0,g))%2==out
        switches+=gauge
        cases.append({'a':list(bits[:3]),'b':list(bits[3:]),'output_disagreement':out,
                      'gauge':gauge,'parent':parent,'active':inc,'cancel_pair':pair})
    # Independent truth-table/physical versus packed coordinate control.
    checks=0
    rng=random.Random(20261025)
    for _ in range(32):
        a=rng.randrange(1,1<<12)
        frame=rng.randrange(-4,5)
        row=decode(a,frame)
        for t in range(25):
            assert row==decode(a,frame+t)
            checks+=1
            row=step(row)
            a=phi(a)
    # For all adjacent output pairs: lexicographic parent cannot cross.
    ordered=0
    for bits in itertools.product((0,1),repeat=8):
        a={x for x,v in zip((-1,0,1,2),bits[:4]) if v}
        b={x for x,v in zip((-1,0,1,2),bits[4:]) if v}
        p=normalization(a,b,0)[0]; q=normalization(a,b,1)[0]
        if p is not None and q is not None:
            assert p<=q
            ordered+=1
    return {'six_bit_cases':64,'two_gauge_identity_checks':128,'gauge_switches':switches,
            'physical_packed_row_comparisons':checks, 'eight_bit_cases':256,
            'adjacent_two_survivor_cases':ordered,'truth_table':cases}

def canonical_run(T,P,horizon, seed_rows, retain=False):
    a=seed_rows[T].copy(); b=seed_rows[T+P].copy()
    labels={x:x for x in a^b}
    initial=sorted(labels)
    target_root=initial[0]
    visits=set()
    if 0 in labels: visits.add(labels[0])
    extinction=None
    first_mismatch=0 if 0 in labels else None
    history=[]
    for t in range(horizon+1):
        if retain:
            history.append({'t':t,'a':sorted(a),'b':sorted(b),
                            'labels':[[x,labels[x]] for x in sorted(labels)],
                            'center_disagreement':int(0 in labels)})
        if t==horizon: break
        an=step(a); bn=step(b)
        next_labels={x:labels[min(p for p in (x-1,x,x+1) if p in labels)] for x in an^bn}
        ordered=[next_labels[x] for x in sorted(next_labels)]
        assert ordered==sorted(ordered)
        assert max(next_labels)==max(labels)+1
        assert next_labels[max(next_labels)]==initial[-1]
        if extinction is None and target_root not in next_labels.values(): extinction=t+1
        labels=next_labels; a=an; b=bn
        if 0 in labels:
            visits.add(labels[0])
            if first_mismatch is None: first_mismatch=t+1
    return {'T':T,'P':P,'horizon':horizon,'initial_roots':initial,
            'leftmost_root':target_root,'leftmost_extinction_time':extinction,
            'leftmost_visits_center':target_root in visits,'center_visited_roots':sorted(visits),
            'first_center_mismatch':first_mismatch,'history':history}

def main():
    start=time.monotonic()
    local=local_controls()
    seed_rows=[{0}]
    for _ in range(40): seed_rows.append(step(seed_rows[-1]))
    failures=[]; sampled=[]
    for total in range(1,33):
        for P in range(1,total+1):
            T=total-P
            if T>16 or P>16: continue
            r=canonical_run(T,P,96,seed_rows)
            sampled.append({k:v for k,v in r.items() if k!='history'})
            if r['leftmost_extinction_time'] is not None and not r['leftmost_visits_center']:
                failures.append((T,P,r['leftmost_extinction_time']))
    first=failures[0] if failures else None
    counter=canonical_run(*first[:2],first[2],seed_rows,True) if first else None
    # Existing cancellation benchmark using the fixed original gauge.
    a={0}; b=step(a); counts={x:1 for x in a^b}; cancellation=[]
    for t in range(4):
        cancellation.append({'time':t,'center_path_count':counts.get(0,0),
                             'center_disagreement':int((0 in a)^(0 in b))})
        an=step(a); bn=step(b)
        n={}
        for x in range(min(a|b)-1,max(a|b)+2):
            weights=[1,int(x+1 not in a),int(x not in b)]
            n[x]=sum(w*counts.get(p,0) for p,w in zip([x-1,x,x+1],weights))
            assert n[x]%2==int((x in an)^(x in bn))
        a,b,counts=an,bn,n
    # Rule90: a deliberately easy periodic-center control, not a new result.
    row={0}; symmetry=[]
    for t in range(257):
        assert row=={-x for x in row}
        assert int(0 in row)==int(t==0)
        symmetry.append({'t':t,'center':int(0 in row),'population':len(row)})
        row=step(row,90)
    out={'description':'Exact finite experiments; no Lean replay or prize claim',
         'local':local,'canonical_bounds':{'T': [0,16],'P':[1,16],'horizon':96},
         'canonical_comparisons':len(sampled),'canonical_runs':sampled,
         'leftmost_root_failures':failures,'minimal_in_order_counterexample':counter,
         'minimality_order':'T+P ascending, then P ascending; restricted rectangle T<=16,P<=16',
         'original_two_path_benchmark':cancellation,
         'rule90_symmetry_control':symmetry,'elapsed_seconds':time.monotonic()-start}
    target=ROOT/'evidence'/'experiment.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'cases':len(sampled),'left_root_failures':len(failures),'first':first,
                      'counterexample':counter,'benchmark':cancellation,'seconds':out['elapsed_seconds']}))

if __name__=='__main__': main()
