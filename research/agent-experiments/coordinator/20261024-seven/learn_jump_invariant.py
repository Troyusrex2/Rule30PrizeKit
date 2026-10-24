"""Exact GF(2) learning of low-degree invariants of the finite return table.

This is a hypothesis generator on 4096 states, not an all-width proof.
"""
import json,time
from core import HERE,save

def first_white(a):
    for s in range(46):
        if s%2==1 and a&1==0:return s
        a=(a>>1)^(a|(a<<1))
    return None

def features(u,index):
    row=0;v=u
    while True:
        i=index[v]
        if i>=0:row|=1<<i
        if not v:return row
        v=(v-1)&u

def fit(table,bad,degree):
    monomials=[m for m in range(4096) if m.bit_count()<=degree]
    index=[-1]*4096
    for i,m in enumerate(monomials):index[m]=i
    vectors=[features(u,index) for u in range(4096)];basis={};equations=0
    def insert(row,rhs):
        nonlocal equations
        equations+=1
        while row:
            p=row.bit_length()-1
            if p not in basis:basis[p]=(row,rhs);return True
            a,b=basis[p];row^=a;rhs^=b
        return rhs==0
    for u,v in enumerate(table):
        assert insert(vectors[u]^vectors[v],0)
    if not insert(vectors[0],0):raise AssertionError('zero constraint')
    for u in bad:
        if not insert(vectors[u],1):
            return {'degree':degree,'variables':len(monomials),'rank':len(basis),
                    'satisfiable':False,'equations_at_contradiction':equations}
    solution=0
    for p,(row,rhs) in sorted(basis.items()):
        bit=rhs^((row&solution).bit_count()&1)
        if bit:solution|=1<<p
    values=[(v&solution).bit_count()&1 for v in vectors]
    assert not values[0] and all(values[u] for u in bad)
    assert all(values[u]==values[v] for u,v in enumerate(table))
    terms=[m for i,m in enumerate(monomials) if solution>>i&1]
    return {'degree':degree,'variables':len(monomials),'rank':len(basis),'satisfiable':True,
            'term_masks':terms,'term_count':len(terms),'zero_class_states':values.count(0),
            'all_table_constraints_exactly_checked':True}

def main():
    start=time.monotonic();data=json.loads((HERE/'jump-table-12-data.json').read_text())
    bad=[u for u,a in enumerate(data['prefix']) if first_white(a) is None]
    out={'states':4096,'bad_prefix_states':len(bad),'records':[],
         'domain':'the fixed 12-bit upper return table only','Lean_verified':False,'full_problem_solved':False}
    for degree in range(1,10):
        before=time.monotonic();r=fit(data['return'],bad,degree);r['seconds']=round(time.monotonic()-before,3)
        out['records'].append(r);save('learned-jump-invariant.json',out)
        print({k:v for k,v in r.items() if k!='term_masks'},flush=True)
        if r['satisfiable']:break
    out['seconds']=round(time.monotonic()-start,3);save('learned-jump-invariant.json',out)

if __name__=='__main__':main()
