from pathlib import Path
from itertools import product
import json
from monodromy_probe import group,structure,search,recover,image
ROOT=Path(__file__).resolve().parent

def direct(w,g,rule):
    elems,e,mul,inv,_=g;tree,free,nt,path,_,edges=structure(w,rule)
    solutions=0
    for values in product(range(len(elems)),repeat=len(free)):
        if all(v==e for v in values):continue
        L=[e]*(1<<w)
        for edge,v in zip(free,values):L[edge]=v
        found=False
        for root in range(len(elems)):
            M=[None]*nt;M[0]=root
            for u,v,ly,lo,_ in path:M[v]=mul[mul[L[ly]][M[u]]][inv[L[lo]]]
            if all(mul[L[ly]][M[u]]==mul[M[v]][L[lo]] for u,v,ly,lo,_ in edges):found=True;break
        if found:solutions+=1
    return solutions

g=group(1,0b10);controls=[]
for rule in [204,240,150,0,30]:
    result=search('SL2_F2',2,g,10,rule)
    literal=direct(2,g,rule)
    positive=result['status']=='nontrivial_candidate'
    assert positive==(literal>0)
    assert positive==(rule in [204,240,150]),(rule,result,literal)
    controls.append({'rule':rule,'nontrivial_solution_exists':positive,'direct_solution_count':literal})
assert direct(3,g,30)==0
for w in range(1,6):
    for word in range(1<<(w+2)):
        assert image(word,w)==sum((((word>>j)&1)^(((word>>(j+1))&1)|((word>>(j+2))&1)))<<j for j in range(w))
(ROOT/'monodromy-controls.json').write_text(json.dumps({'controls':controls,'direct_width3_rule30':False,'rule30_truth_table_agrees':True},indent=2)+'\n')
print('positive_controls_identity_shift_parity_passed; negative_controls_zero_rule30_passed; direct_enumeration_agrees')
