"""Independent cellwise checks of the finite certificates behind the theorem.

The all-position conclusion is proved in Lean, not inferred from these samples.
"""
import json
from pathlib import Path


def rows(rule,steps):
    history=[{0:1}]
    for t in range(steps):
        old=history[-1]
        history.append({p:(rule>>((old.get(p-1,0)<<2)|(old.get(p,0)<<1)|old.get(p+1,0)))&1
                        for p in range(-t-1,t+2)})
    return history


def main():
    history=rows(30,530)
    left=[];right=[]
    a=b=1;mask=(1<<20)-1
    for t,row in enumerate(history):
        l=sum(row.get(-t+j,0)<<j for j in range(20))
        r=sum(row.get(t-j,0)<<j for j in range(20))
        assert l==a and r==b
        left.append(l);right.append(r)
        a=((a<<2)^((a<<1)|a))&mask
        b=(b^((b<<1)|(b<<2)))&mask
    assert right[256]==right[0]==1
    assert left[24]==left[20]
    lags=[]
    for residue in range(256):
        good=[j for j in range(19) if ((left[20+(residue+j)%4]^right[(residue+j)%256])>>j)&1]
        assert good
        lags.append(good[0])
    first={}
    for m in range(1,513):
        good=[j for j in range(19) if history[m+j].get(-m,0)!=history[m+j].get(m,0)]
        assert good
        first[m]=good[0]
    assert first[256]==18
    pairs=0
    for p in range(-24,25):
        for q in range(p+1,25):
            assert any(history[t].get(p,0)!=history[t].get(q,0)
                       for t in range(max(abs(p),abs(q))+19))
            pairs+=1
    for rule in [90,150]:
        control=rows(rule,80)
        assert all(row.get(-m,0)==row.get(m,0) for row in control for m in range(1,33))
    report={'finite_crosschecks_only':True,'all_positions_theorem_requires_Lean':True,
            'cellwise_rows_checked':len(history),'front_width':20,
            'left_transient':20,'left_period':4,'left_cycle':left[20:24],
            'right_period':256,'periodic_residue_classes_checked':256,
            'sample_mirror_pairs':512,'largest_sample_lag':max(first.values()),
            'example_m256_lag':first[256],'sample_distinct_column_pairs':pairs,
            'negative_controls':[90,150],'verdict':'pass'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__':main()
