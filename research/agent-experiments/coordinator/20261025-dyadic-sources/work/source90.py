"""Exact run-boundary-source decomposition. No unbounded no-cancellation claim."""
from pathlib import Path
import json, time
from wall_tools import physical_center

root=Path(__file__).resolve().parent
start=time.monotonic()
def phi(a): return (a<<2) ^ ((a<<1)|a)
def linear(a): return (a<<2)^a
def source(a): return (a<<1)&~a
def power(a,n):
    bit=0
    while n:
        if n&1: a ^= a << (2<<bit)
        n >>= 1; bit += 1
    return a
def allones(n): return int(n>0 and (n&(n+1))==0)

# Direct local truth-table controls, not just the sampled seed trajectory.
for a in range(4096): assert phi(a)==linear(a)^source(a)
rows=[1]
for _ in range(128): rows.append(phi(rows[-1]))
assert [a>>t&1 for t,a in enumerate(rows)] == physical_center(30,129)
convolution_checks=0
event_witnesses={}
for n in range(1,129):
    full=edge=0
    for s in range(n):
        full ^= power(source(rows[s]),n-1-s)
        edge ^= power(1<<(2*s+1),n-1-s)
    assert rows[n]==power(1,n)^full
    assert (edge>>n&1)==allones(n)
    convolution_checks += 1
    if n in [3,7,15]:
        events=[]
        for s in range(n):
            h=n-1-s
            src=source(rows[s])
            for j in range(n+1):
                if not(src>>j&1) or (n-j)%2: continue
                q=(n-j)//2
                if q&h==q:
                    events.append({'time':s,'source_bit':j,'physical_position':j-s-1,
                                   'outer_wall':j==2*s+1})
        assert len(events)%2 == (full>>n&1)
        event_witnesses[str(n)]=events

N=65536
a=lin=1; outer=interior=0
center_bits=[]; outer_bits=[]; interior_bits=[]
dyadic=[]; counts={'full_polynomial_decompositions':0,'outer_closed_formula':0,
                  'interior_cancels_odd_outer':0,'interior_survives_zero_outer':0}
for t in range(N):
    assert a==lin^outer^interior
    assert outer == (lin ^ (1<<(2*t))) << 1
    c=a>>t&1; e=outer>>t&1; q=interior>>t&1
    assert (lin>>t&1)==int(t==0)
    assert e==allones(t)
    counts['full_polynomial_decompositions']+=1
    counts['outer_closed_formula']+=1
    if e and q: counts['interior_cancels_odd_outer']+=1
    if not e and q: counts['interior_survives_zero_outer']+=1
    center_bits.append(c); outer_bits.append(e); interior_bits.append(q)
    if t>0 and ((t&(t+1))==0 or (t&(t-1))==0):
        dyadic.append({'time':t,'center':c,'outer':e,'interior':q})
    s=source(a); edge=1<<(2*t+1)
    assert s&edge
    lin=linear(lin)
    outer=linear(outer)^edge
    interior=linear(interior)^(s^edge)
    a=phi(a)
assert bytes(center_bits)==(root/'center-65536.bin').read_bytes()
for label,bits in [('outer90',outer_bits),('interior90',interior_bits)]:
    (root/(label+'-65536.bin')).write_bytes(bytes(bits))
out={'claim':'finite exact diagnostics; no proof of unbounded uncancelled sources',
     'packing':'bit i at time t is physical position i-t',
     'local_formula':'Phi(a)=L90(a) XOR S90(a), L90=(a<<2) XOR a, S90=(a<<1) AND NOT a',
     'outer_source':'bit 2*s+1 at source time s, physical site s',
     'outer_polynomial_identity':'Outer_n(x)=x*((1+x^2)^n+x^(2n)) over GF(2); geometric sum since (1+x^2)+x^2=1',
     'closed_formula_candidate':'outer center parity is 1 exactly at positive times 2^k-1',
     'closed_formula_explanation':'For n=2m+1 the boundary sum is sum(k=0..m) binom(m+k,k)=binom(2m+1,m) mod 2; Lucas gives m AND (m+1)=0. Even n give zero by parity. Elementary derivation, not Lean replayed.',
     'controls':{'truth_table_rows':4096,'physical_center_steps':129,'direct_polynomial_convolutions':convolution_checks},
     'counts':counts,'dyadic':dyadic,'small_source_events':event_witnesses,
     'counterexample_to_odd_boundary_survival':{'time':7,'center':center_bits[7],'outer':outer_bits[7],'interior':interior_bits[7]},
     'elapsed_seconds':time.monotonic()-start,'new_kernel_verified_declarations':0}
(root/'source90.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'counts':counts,'counterexample':out['counterexample_to_odd_boundary_survival'],
                  'small_events_n7':event_witnesses['7'],'elapsed_seconds':out['elapsed_seconds']},indent=2))
