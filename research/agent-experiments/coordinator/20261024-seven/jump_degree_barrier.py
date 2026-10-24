"""Construct and independently replay a finite low-degree learner obstruction.

The edge certificate shows every degree<=8 J-invariant polynomial takes the
same value at 0 and bad state928. This is not a Lean theorem or an all-width
claim. The vertex parity also lies in the degree<=3 Reed-Muller dual code.
"""
import json,time
from core import HERE,save
from learn_jump_invariant import features,first_white

def main():
    before=time.monotonic();data=json.loads((HERE/'jump-table-12-data.json').read_text())
    J=data['return'];mons=[m for m in range(4096) if m.bit_count()<=8];index=[-1]*4096
    for i,m in enumerate(mons):index[m]=i
    fs=[features(u,index) for u in range(4096)];basis={}
    for u,v in enumerate(J):
        row=fs[u]^fs[v];witness=1<<u
        while row:
            p=row.bit_length()-1
            if p not in basis:basis[p]=(row,witness);break
            a,b=basis[p];row^=a;witness^=b
    row=fs[0]^fs[928];edges=0
    while row:
        p=row.bit_length()-1;assert p in basis
        a,b=basis[p];row^=a;edges^=b
    selected=[u for u in range(4096) if edges>>u&1]
    # Independently replay the proposed relation, without the elimination basis.
    replay=0;vertices=(1<<0)^(1<<928)
    for u in selected:
        replay^=fs[u]^fs[J[u]];vertices^=(1<<u)^(1<<J[u])
    assert replay==fs[0]^fs[928] and first_white(data['prefix'][928]) is None
    parity=[(vertices>>u)&1 for u in range(4096)]
    for bit in range(12):
        for u in range(4096):
            if u>>bit&1:parity[u]^=parity[u^(1<<bit)]
    terms=[u for u,b in enumerate(parity) if b]
    assert max(m.bit_count() for m in terms)<=3
    # Independent direct monomial moments of the parity vector.
    support=[u for u in range(4096) if vertices>>u&1]
    assert all(sum((u&m)==m for u in support)%2==0 for m in mons)
    out={'states':4096,'degree_limit':8,'indistinguishable_states':[0,928],
         'state928_fails_the_prefix_white_test':True,'selected_edges':selected,
         'edge_count':len(selected),'dual_vertex_count':len(support),
         'dual_polynomial_terms':terms,'dual_polynomial_degree':3,
         'dual_polynomial_term_count':len(terms),'direct_moments_checked':len(mons),
         'all_certificate_checks_passed':True,'Lean_verified':False,
         'full_problem_solved':False,'seconds':round(time.monotonic()-before,3)}
    save('jump-degree-barrier.json',out)
    print({k:v for k,v in out.items() if k not in ('selected_edges','dual_polynomial_terms')},flush=True)

if __name__=='__main__':main()
