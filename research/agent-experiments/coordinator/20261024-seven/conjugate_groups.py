"""Probe nonlinear finite permutation groups from conjugated low-bit flips.

g_t=Phi^t * flip0 * Phi^(-t) on a finite binary prefix. Rule90 supplies a
linear, commuting control. These finite groups are not a prize premise.
"""
import argparse,random,time
import numpy as np
from sympy.combinatorics import Permutation,PermutationGroup
from core import phi,save

def forward(x,rule):
    return phi(x) if rule==30 else x^(x<<2)

def tables(w,rule):
    n=1<<w;mask=n-1;P=np.array([forward(x,rule)&mask for x in range(n)],dtype=np.int64)
    inv=np.empty(n,dtype=np.int64);inv[P]=np.arange(n)
    assert np.all(P[inv]==np.arange(n))
    return P,inv

def conjugates(w,k,rule):
    P,inv=tables(w,rule);g=np.arange(1<<w,dtype=np.int64)^1;out=[]
    for t in range(k+1):
        out.append(g.copy());g=P[g[inv]]
    return out

def controls(k,rule,gs):
    rng=random.Random(304731+k+rule);w=2*k+1;wide=w+5
    P,inv=tables(wide,rule);mask=(1<<w)-1;cases=0
    for t,g in enumerate(gs):
        for _ in range(32):
            x=rng.randrange(1<<wide);y=x
            for _ in range(t):y=int(inv[y])
            y^=1
            for _ in range(t):y=int(P[y])
            assert y==(x&~mask)|int(g[x&mask]);cases+=1
    return cases

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--max-k',type=int,default=4)
    args=parser.parse_args();out={'records':[],'finite_experiment_only':True,
                                  'Lean_verified':False,'full_problem_solved':False}
    for k in range(args.max_k+1):
        w=2*k+1
        for rule in (90,30):
            start=time.monotonic();gs=conjugates(w,k,rule)
            checks=controls(k,rule,gs)
            G=PermutationGroup([Permutation(list(map(int,g))) for g in gs])
            order=int(G.order());assert order&(order-1)==0
            if rule==90:assert order==1<<(k+1) and G.is_abelian
            derived=[];D=G
            while D.order()>1:
                derived.append(int(D.order()));D=D.derived_subgroup()
                assert len(derived)<=w
            row={'max_conjugate_time':k,'prefix_width':w,'rule':rule,
                 'group_order':order,'group_order_log2':order.bit_length()-1,
                 'abelian':G.is_abelian,'derived_subgroup_orders':derived,
                 'derived_length':len(derived),'orbit_of_zero':len(G.orbit(0)),
                 'independent_wide_controls':checks,'seconds':round(time.monotonic()-start,3)}
            out['records'].append(row);save('conjugate-groups.json',out);print(row,flush=True)

if __name__=='__main__':main()
