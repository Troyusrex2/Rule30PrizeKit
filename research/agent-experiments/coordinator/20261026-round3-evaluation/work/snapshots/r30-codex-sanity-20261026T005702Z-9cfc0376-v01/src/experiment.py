"""Periodic-tail surgery: exact finite inverse-trace experiments, not a proof."""
import hashlib
import json
import sys
import time
from pathlib import Path

OUT = Path(sys.argv[1]).resolve()
OUT.mkdir(parents=True, exist_ok=True)
START = time.monotonic()

def g(c, r, rule):
    if rule == 30: return c | r
    if rule == 90: return r
    if rule == 150: return c ^ r
    if rule == 210: return (~c) & r
    raise ValueError(rule)

def forward(seed, n, rule=30):
    a, trace = seed, 0
    for t in range(n):
        trace |= ((a >> t) & 1) << t
        a = a ^ g(a << 1, a << 2, rule)
    return trace

def inverse_trace(u, n, rule=30):
    # Initial positions p>=1 are white. Bit t packs time along a column.
    r, right = 0, 0
    for t in range(n):
        right |= (r & 1) << t
        r = (r << 1) ^ ((u >> t) & 1) ^ g(r, r >> 1, rule)
    center = u
    seed = u & 1
    for m in range(1, n):
        left = ((center >> 1) ^ g(center, right, rule)) & ((1 << (n-m))-1)
        seed |= (left & 1) << m
        right, center = center, left
    return seed

def physical(seed, n, rule):
    row = {-i:1 for i in range(seed.bit_length()) if (seed >> i) & 1}
    out = 0
    for t in range(n):
        out |= row.get(0,0) << t
        lo, hi = min(row,default=0)-1, max(row,default=0)+1
        row = {p:1 for p in range(lo,hi+1)
               if (rule >> ((row.get(p-1,0)<<2)|(row.get(p,0)<<1)|row.get(p+1,0))) & 1}
    return out

def lsb(x, n):
    return ''.join(str((x >> i) & 1) for i in range(n))

def surgery(c, t, p, n):
    return sum(((c >> (i if i < t else t+(i-t)%p)) & 1) << i for i in range(n))

def first_set(x):
    return (x & -x).bit_length()-1 if x else None

def main():
    controls = 0
    for rule in (30,90,150,210):
        for u in range(128):
            b = inverse_trace(u,7,rule)
            assert physical(b,7,rule) == u == forward(b,7,rule)
            controls += 1
    n = 2048
    c = forward(1,n)
    assert inverse_trace(c,n) == 1
    (OUT/'center.bits').write_text(lsb(c,n)+'\n',encoding='ascii')
    records = []
    strong_failures = []
    short_window_failure = None
    annuli_checked = 0
    for t in range(17):
        for p in range(1,17):
            u = surgery(c,t,p,n)
            b = inverse_trace(u,n)
            assert forward(b,n) == u
            assert b & 1
            first = first_set(b ^ 1)
            assert first == first_set(u ^ c)
            for prefix in (31,64,128,512):
                assert inverse_trace(u & ((1<<prefix)-1),prefix) == b & ((1<<prefix)-1)
            m = 2*(t+p+1)
            annuli = []
            while 2*m <= n:
                count = ((b >> m) & ((1<<m)-1)).bit_count()
                annuli.append({'start':m,'end_exclusive':2*m,'black_seed_edits':count})
                annuli_checked += 1
                if count == 0: strong_failures.append({'T':t,'P':p,'start':m,'end_exclusive':2*m})
                m *= 2
            if short_window_failure is None:
                for m in range(t+p,n-p+1):
                    if ((b>>m)&((1<<p)-1)) == 0:
                        short_window_failure={'T':t,'P':p,'start':m,'length':p}
                        break
            records.append({'T':t,'P':p,'forced_period_word':lsb((c>>t)&((1<<p)-1),p),
                            'first_extra_seed_cell_depth':first,'edits_excluding_origin':b.bit_count()-1,
                            'reconstructed_seed_lsb_first':lsb(b,n),'annuli':annuli})
    barrier_controls=[]
    for rule in (90,150,210):
        cr = forward(1,n,rule)
        u = surgery(cr,1,1,n)
        assert u == cr
        b = inverse_trace(u,n,rule)
        assert b == 1 and forward(b,n,rule)==u
        barrier_controls.append({'rule':rule,'T':1,'P':1,'inverse_seed':1,'additional_edits':0})
    result={'status':'completed_exact_finite_computation','center_bits':n,
            'center_sha256':hashlib.sha256((OUT/'center.bits').read_bytes()).hexdigest(),
            'physical_inverse_truth_table_cases':controls,'surgery_cases':len(records),
            'annuli_checked':annuli_checked,'fixed_M_rule':'M=2*(T+P+1); annuli [M*2^k,M*2^(k+1))',
            'fixed_M_failures':strong_failures,'one_edit_per_period_window_counterexample':short_window_failure,
            'linear_or_barrier_controls':barrier_controls,'cases':records,
            'seconds':time.monotonic()-START}
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
    print('First 12 surgery summaries:',json.dumps([{k:v for k,v in r.items() if k not in ('reconstructed_seed_lsb_first','annuli')} for r in records[:12]]))

if __name__ == '__main__': main()
