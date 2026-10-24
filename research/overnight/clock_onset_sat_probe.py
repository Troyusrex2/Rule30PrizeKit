"""Falsify extending the local clock theorem through arbitrary prefixes.

Only discovery: SAT models are independently checked, and bounded UNSAT is
not promoted to an unbounded theorem. Periodic right tails need not be finite.
"""
import argparse
import json
from pathlib import Path
import time

import z3


def derivative(x,p):return x^((x>>1)|((x&1)<<(p-1)))


def scalar_check(prefix,tail,p):
    def profile(k):return prefix[k] if k<len(prefix) else tail[(k-len(prefix))%len(tail)]
    h=4*p;window=len(prefix)+2*len(tail)+4
    row=sum((profile(k)&1)<<k for k in range(2*h+window+2))
    for t in range(h):
        for k in range(window):assert (row>>k)&1==(profile(k)>>(t%p))&1
        row^=(row>>1)|(row>>2)
    return h*window


def probe(half,n,m,lower_tail=True,timeout=10000,zero_tail=False,head_loss=True):
    began=time.monotonic();p=2*half;solver=z3.Solver()
    solver.set(timeout=timeout,threads=2,max_memory=1024)
    prefix=[z3.BitVec('a'+str(i),p) for i in range(n)]
    tail=[z3.BitVec('b'+str(i),half if lower_tail else p) for i in range(m)]
    repeated=[z3.Concat(b,b) if lower_tail else b for b in tail]
    column=lambda i:prefix[i] if i<n else repeated[(i-n)%m]
    for i,a in enumerate(prefix):solver.add(a^z3.RotateRight(a,1)==column(i+1)|column(i+2))
    for i,b in enumerate(tail):solver.add(b^z3.RotateRight(b,1)==tail[(i+1)%m]|tail[(i+2)%m])
    is_small=lambda a:z3.Extract(half-1,0,a)==z3.Extract(p-1,half,a)
    solver.add(is_small(prefix[0]) if head_loss else z3.Not(is_small(prefix[0])))
    solver.add(z3.Or(*[z3.Not(is_small(a)) for a in prefix]))
    if zero_tail:solver.add(*[b==0 for b in tail])
    verdict=solver.check()
    result={'half_clock':half,'clock':p,'prefix_columns':n,'tail_spatial_period':m,
            'tail_half_clock_imposed':lower_tail,'zero_tail_control':zero_tail,
            'head_clock_drop_required':head_loss,
            'verdict':str(verdict),'seconds':round(time.monotonic()-began,3),
            'Lean_verified':False,'full_problem_claim':False,'bounded_query_only':True}
    if verdict==z3.sat:
        model=solver.model();aa=[model.eval(a,model_completion=True).as_long() for a in prefix]
        bb=[model.eval(b,model_completion=True).as_long() for b in tail]
        if lower_tail:bb=[b|(b<<half) for b in bb]
        assert (aa[0]&((1<<half)-1)==aa[0]>>half)==head_loss
        assert any(a&((1<<half)-1)!=a>>half for a in aa)
        for i,a in enumerate(aa):
            get=lambda k:aa[k] if k<len(aa) else bb[(k-len(aa))%len(bb)]
            assert derivative(a,p)==get(i+1)|get(i+2)
        for i,b in enumerate(bb):assert derivative(b,p)==bb[(i+1)%m]|bb[(i+2)%m]
        result.update(prefix_profiles=aa,tail_profiles=bb,
                      independent_scalar_cells_checked=scalar_check(aa,bb,p),all_model_checks_passed=True,
                      tail_is_zero=all(b==0 for b in bb),finite_support_claim=False)
    elif verdict==z3.unknown:result['reason']=solver.reason_unknown()
    return result


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--seconds',type=int,default=10)
    args=ap.parse_args();results=[];path=Path(__file__).with_suffix('.json')
    cases=[(4,4,4,False,False,True),(4,12,4,True,False,True),
           (16,10,1,True,True,False),(16,16,1,True,True,True)]
    cases += [(16,n,m,True,False,True) for n,m in [(12,4),(16,4),(24,4),(12,8),(16,8),(24,8),(16,12),(24,12),(24,16)]]
    for half,n,m,lower,zero,head_loss in cases:
        result=probe(half,n,m,lower,args.seconds*1000,zero,head_loss)
        results.append(result);print(json.dumps(result),flush=True)
        path.write_text(json.dumps({'Lean_verified':False,'full_problem_claim':False,
            'unbounded_extension_proved':False,'results':results},indent=2)+'\n',encoding='utf-8',newline='\n')
        if result['verdict']=='sat' and lower and head_loss:break
    assert results[0]['verdict']=='sat','Positive encoding control did not pass'
    assert results[2]['verdict']=='sat','Actual period-doubling positive control did not pass'


if __name__=='__main__':main()
