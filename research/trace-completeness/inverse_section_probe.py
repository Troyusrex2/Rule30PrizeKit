"""Explore finite-state sections of the one-bit trace-preserving branch flip.

This is a finite complexity probe, not a completeness theorem.
"""
from pathlib import Path
import importlib.util
import json
import random
import time

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('inverse_probe',HERE/'inverse_trace_gap_probe.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

def flip(b,n):
    return m.inverse(m.trace(b,1,n-1),1,1-(b&1),n-1)[0]

def main():
    start=time.monotonic()
    h=8192;tailbits=4096
    samples=[]
    for b in [0,1,2,3,7,13,25,45,49]:
        a,ones=m.inverse(m.trace(b,1,h),1,1-(b&1),h)
        tail=(a>>(1+h-tailbits))&((1<<tailbits)-1)
        periods=[p for p in range(1,129) if ((tail^(tail>>p))&((1<<(tailbits-p))-1))==0]
        samples.append({'target_row':b,'prefix_ones':ones[:24],
                        'total_ones':len(ones),'tail_bits':tailbits,'tail_ones':tail.bit_count(),
                        'tail_periods_at_most_128':periods[:8],
                        'last_required_one':ones[-1],
                        'no_required_ones_beyond_target_width_in_window':all(i<b.bit_length() for i in ones)})
    k=5;depth=10;n=k+depth
    outputs=[flip(b,n) for b in range(1<<n)]
    mask=(1<<n)-1
    assert all(outputs[outputs[b]]==b for b in range(1<<n))
    rng=random.Random(3001)
    for _ in range(200):
        length=rng.randrange(2,n+1);b=rng.randrange(1<<length)
        assert flip(b,length)==outputs[b]&((1<<length)-1)
    sections=[]
    for d in range(depth+1):
        signatures={tuple((outputs[p|(s<<d)]>>d)&((1<<k)-1) for s in range(1<<k))
                    for p in range(1<<d)}
        sections.append({'prefix_depth':d,'suffix_depth':k,'distinct_residual_maps':len(signatures)})
    result={'finite_experiment_only':True,'Lean_verified':False,'full_problem_solved':False,
            'temporal_horizon':h,'spatial_tail_samples':samples,'finite_section_counts':sections,
            'prefix_consistency_controls':200,'prefix_involution_domain':1<<n,
            'seconds':round(time.monotonic()-start,3)}
    (HERE/'inverse-section-probe.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(result),flush=True)

if __name__=='__main__':main()
