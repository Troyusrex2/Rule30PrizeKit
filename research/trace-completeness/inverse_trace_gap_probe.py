"""Falsify edge horizons using exact finite inverse-cone reconstruction.

Finite experiment only. A long zero tail is not assumed to stay zero.
"""
import json
from pathlib import Path
import random
import time
import psutil

HERE=Path(__file__).resolve().parent

def phi(a):return a ^ ((a<<1)|(a<<2))

def trace(a,c,h):
    bits=0
    for t in range(h):
        bits |= ((a>>(c+t))&1)<<t
        a=phi(a)
    return bits

def prefix_xor(bits,mask,h):
    shift=1
    while shift<h:
        bits=(bits ^ (bits<<shift))&mask
        shift<<=1
    return bits

def inverse(target,c,right,h):
    assert 0<=right<1<<c
    mask=(1<<h)-1
    previous=previous2=0
    initial=0
    ones=[]
    for i in range(c+h):
        base=prefix_xor(((previous|previous2)<<1)&mask,mask,h)
        bit=((right>>i)&1) if i<c else ((base>>(i-c)) ^ (target>>(i-c)))&1
        if bit:
            initial|=1<<i
            ones.append(i)
        current=base ^ (mask if bit else 0)
        previous2,previous=previous,current
    return initial,ones

def main():
    start=time.monotonic();process=psutil.Process()
    rng=random.Random(303011)
    controls=0
    for b,c,right,expected in [(3,1,0,2),(2,1,1,3),(45,5,13,45),(45,5,1,None),(25,4,1,None)]:
        h=160
        target=trace(b,c,h)
        a,ones=inverse(target,c,right,h)
        assert trace(a,c,h)==target
        assert a&((1<<c)-1)==right
        if expected is not None:assert a==expected,(b,c,right,a)
        if b==45 and right==1:assert next(i for i in ones if i>5)==63
        if b==25 and right==1:assert next(i for i in ones if i>4)==20
        controls+=1
    cases=[(45,5,1),(25,4,1),(48,3,1),(7,1,0),(1,3,1),(0,4,1)]
    old=json.loads((HERE/'edge-completeness-width-probe.json').read_text())
    for record in old['results']:
        pair=record.get('maximal_delay_witness')
        if pair:
            a,b=pair;c=record['center_index']
            cases.extend([(b,c,a&((1<<c)-1)),(a,c,b&((1<<c)-1))])
    cases=list(dict.fromkeys(cases))
    for _ in range(400):
        c=rng.randrange(2,13)
        b=rng.getrandbits(rng.randrange(c+1,c+14)) or 1
        right=rng.randrange(1<<c)
        cases.append((b,c,right))
    h=4096
    results=[];counters=[];best=None
    stopped=None
    for index,(b,c,right) in enumerate(cases):
        if (time.monotonic()-start>100 or process.memory_info().rss>2*1024**3
                or psutil.virtual_memory().available<2*1024**3):
            stopped='resource guard; partial experiment';break
        target=trace(b,c,h)
        a,ones=inverse(target,c,right,h)
        assert trace(a,c,h)==target,(b,c,right)
        assert a&((1<<c)-1)==right
        edge=b.bit_length()-1
        selected=[]
        endpoints=list(zip(ones,ones[1:]))
        if ones:endpoints.append((ones[-1],c+h))
        for last,next_one in endpoints:
            if last==edge or next_one<=c or b==0:continue
            # Truncation below next_one agrees up to time next_one-c-1.
            initial=a & ((1<<(last+1))-1)
            n=max(last+1,b.bit_length(),c+1)
            delay=next_one-c
            if best is None or delay/(2*n+2)>best['ratio']:
                best={'target_row':b,'center_index':c,'right_prefix':right,
                      'last_one':last,'next_one':next_one,'first_difference_time':delay,
                      'candidate_horizon':2*n+2,'ratio':delay/(2*n+2)}
            if delay>=2*n+2:
                # This is a concrete finite counterexample to the proposed bound,
                # not an infinite-trace collision. Recheck using direct integers.
                da=trace(initial,c,min(delay+1,h))^trace(b,c,min(delay+1,h))
                if delay<h:assert da and (da&-da).bit_length()-1==delay
                else:assert da==0
                counter={'rows':[initial,b],'center_index':c,'initial_bit_bound':n,
                         'candidate_horizon':2*n+2,'agreed_observations':delay,
                         'first_difference_time':delay if delay<h else None}
                counters.append(counter);selected.append(counter)
        results.append({'target_row':b,'center_index':c,'right_prefix':right,
                        'required_ones':len(ones),'last_required_one':ones[-1] if ones else None,
                        'first_ones':ones[:20],'counterexamples':selected})
        if counters:stopped='finite horizon counterexample found';break
    report={'finite_experiment_only':True,'Lean_verified':False,'inverse_controls':controls,
            'inverse_time_horizon':h,'cases_checked':len(results),'results':results,
            'candidate_counterexamples':counters,'largest_delay_ratio':best,
            'stopped_reason':stopped,'finite_zero_tail_not_assumed_permanent':True,
            'edge_observability_proved':False,'full_problem_solved':False,
            'seconds':round(time.monotonic()-start,3)}
    (HERE/'inverse-trace-gap-probe.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k!='results'}),flush=True)

if __name__=='__main__':main()
