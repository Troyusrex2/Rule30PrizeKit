"""Try to refute finite-even-support exclusion using periodic golden free bits.

Periodic temporal rows reconstruct through a finite spatial machine. A closed
spatial cycle with zero even cells in one even temporal phase would give a
candidate counterexample to the stronger route, not to Q01.
"""
import argparse,time
from core import save
from even_code_charge import words
from coupled_even_code_probe import forbidden,decode,even_code

def rotate(w,p,q):return ((w>>q)|(w<<(p-q)))&((1<<p)-1) if q else w

def orbit(w,p,cap):
    P=2*p;head=sum((1 if t%2==0 else (w>>(t//2))&1)<<t for t in range(P))
    def rot(a):return (a>>1)|((a&1)<<(P-1))
    a=0;b=head;seen={};history=[]
    for d in range(cap+1):
        key=a|(b<<P)
        if key in seen:
            mu=seen[key];cycle=history[mu:];union=0
            for x,y in cycle:union|=x
            phases=[q for q in range(p) if not(union>>(2*q)&1)]
            row={'period':p,'free_word':w,'complete_spatial_cycle':True,
                 'preperiod':mu,'spatial_pair_period':d-mu,'phases_with_finite_even_support':phases}
            for q in {0,p-1}:
                free=[(w>>((j+q)%p))&1 for j in range(64)]
                u=0
                for j in range(1,65):
                    at=j if j<len(history) else mu+(j-mu)%(d-mu)
                    u|=((history[at][0]>>(2*q))&1)<<(j-1)
                assert even_code(free)==u and decode(u,64)==free
            row['independent_decoder_prefix_controls']=64*len({0,p-1})
            if phases:
                q=phases[0];u=sum(((history[j][0]>>(2*q))&1)<<(j-1) for j in range(1,mu))
                free=[(w>>((j+q)%p))&1 for j in range(128)]
                assert forbidden(free) is None and decode(u,128)==free
                row['candidate']={'finite_even_input':u,'free_rotation':q,'head_period':P,
                                  'spatial_prefix_and_cycle':history}
            return row
        seen[key]=d;history.append((a,b))
        a2=rot(b)^(b|a);b2=rot(a2)^(a2|b);a,b=a2,b2
    return {'period':p,'free_word':w,'complete_spatial_cycle':False,'steps_checked':cap}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--max-period',type=int,default=12)
    parser.add_argument('--spatial-cap',type=int,default=100000);args=parser.parse_args()
    start=time.monotonic();out={'records':[],'Lean_verified':False,'full_problem_solved':False,
                                  'counterexample_to_Q01':False}
    for p in range(1,args.max_period+1):
        candidates=[]
        for w in words(p,True):
            if forbidden([(w>>(i%p))&1 for i in range(p+4)]) is not None:continue
            if w!=min(rotate(w,p,q) for q in range(p)):continue
            if any(p%q==0 and all((w>>i&1)==(w>>(i%q)&1) for i in range(p)) for q in range(1,p)):continue
            candidates.append(w)
        for w in candidates:
            row=orbit(w,p,args.spatial_cap);out['records'].append(row)
            save('periodic-golden-even.json',out)
            if row.get('candidate'):
                print({k:v for k,v in row.items() if k!='candidate'},flush=True);return
        print({'free_period':p,'primitive_rotation_classes':len(candidates),
               'cycles_complete':sum(r['complete_spatial_cycle'] for r in out['records'] if r['period']==p),
               'seconds':round(time.monotonic()-start,3)},flush=True)
        if time.monotonic()-start>180:break
    out['seconds']=round(time.monotonic()-start,3);save('periodic-golden-even.json',out)

if __name__=='__main__':main()
