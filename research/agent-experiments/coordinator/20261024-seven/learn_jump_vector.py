"""Find a vector of small invariant polynomials, instead of one scalar bit.

Exact on the fixed 4096-state table. No statement about larger windows.
"""
import json,time
from core import HERE,save
from learn_jump_invariant import features,first_white

def fit(table,bad,degree):
    mons=[m for m in range(4096) if m.bit_count()<=degree];index=[-1]*4096
    for i,m in enumerate(mons):index[m]=i
    vectors=[features(u,index) for u in range(4096)];basis={}
    def reduce(row):
        for p in sorted(basis,reverse=True):
            if row>>p&1:row^=basis[p]
        return row
    for u,v in enumerate(table):
        row=vectors[u]^vectors[v]
        while row:
            p=row.bit_length()-1
            if p not in basis:basis[p]=row;break
            row^=basis[p]
    residuals=[reduce(vectors[u]^vectors[0]) for u in bad]
    unresolved=[u for u,r in zip(bad,residuals) if r==0]
    out={'degree':degree,'monomials':len(mons),'invariance_rank':len(basis),
         'bad_states_sharing_every_low_degree_invariant_with_zero':unresolved,
         'all_bad_states_separated':not unresolved}
    if unresolved:return out
    remaining=set(range(len(bad)));chosen=[]
    free=[i for i in range(len(mons)) if i not in basis]
    while remaining:
        v=max(free,key=lambda i:sum((residuals[j]>>i)&1 for j in remaining))
        covered={j for j in remaining if residuals[j]>>v&1};assert covered
        solution=1<<v
        for p,row in sorted(basis.items()):
            if (row&solution).bit_count()&1:solution|=1<<p
        if (vectors[0]&solution).bit_count()&1:solution^=1<<index[0]
        values=[(r&solution).bit_count()&1 for r in vectors]
        assert values[0]==0 and all(values[u]==values[t] for u,t in enumerate(table))
        assert all(values[bad[j]] for j in covered)
        terms=[m for i,m in enumerate(mons) if solution>>i&1]
        chosen.append({'term_masks':terms,'term_count':len(terms),
                       'new_bad_states_separated':len(covered)})
        remaining-=covered;free.remove(v)
    allowed=[u for u in range(4096) if all(
        sum((u&m)==m for m in p['term_masks'])%2==0 for p in chosen)]
    assert 0 in allowed and not set(allowed)&set(bad)
    assert all(table[u] in allowed for u in allowed)
    out.update({'selected_invariants':chosen,'invariant_count':len(chosen),
                'total_term_count':sum(p['term_count'] for p in chosen),
                'zero_class_states':len(allowed),'all_table_constraints_exactly_checked':True})
    return out

def main():
    start=time.monotonic();data=json.loads((HERE/'jump-table-12-data.json').read_text())
    bad=[u for u,a in enumerate(data['prefix']) if first_white(a) is None]
    out={'states':4096,'bad_states':len(bad),'records':[],'Lean_verified':False,
         'domain':'fixed 12-bit return table only','full_problem_solved':False}
    for d in range(1,10):
        row=fit(data['return'],bad,d);out['records'].append(row)
        save('learned-jump-vector.json',out)
        print({k:v for k,v in row.items() if k not in
               ('selected_invariants','bad_states_sharing_every_low_degree_invariant_with_zero')},flush=True)
        if row['all_bad_states_separated']:break
    out['seconds']=round(time.monotonic()-start,3);save('learned-jump-vector.json',out)

if __name__=='__main__':main()
