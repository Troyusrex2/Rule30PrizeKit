"""A finite-type overapproximation of an exact finite boundary image.

The automaton counts words avoiding the observed finite list of obstructions.
It is not identified with the true infinite image language.
"""
import argparse,json
import numpy as np
from core import HERE,save
from even_code_charge import words

def main():
    p=argparse.ArgumentParser();p.add_argument('--image-length',type=int,default=20);a=p.parse_args()
    n=a.image_length;ref=json.loads((HERE/f'right-image-smt-{n}.json').read_text(encoding='utf-8'))
    assert ref['finite_census_complete']
    image={int(w) for w in ref['image_witnesses']};forbidden=['00','11111'];by_length={}
    for k in range(1,n+1):
        allowed={w&((1<<k)-1) for w in image}
        by_length[str(k)]=len(allowed)
        for v in sorted(set(words(k,True))-allowed):
            s=''.join(str(v>>i&1) for i in range(k))
            if any(q in s for q in forbidden):continue
            forbidden.append(s)
    prefixes={''}
    for q in forbidden:prefixes.update(q[:j] for j in range(len(q)))
    states=sorted(prefixes,key=lambda s:(len(s),s));index={s:i for i,s in enumerate(states)};edges=[]
    for s in states:
        out=[]
        for c in ['0','1']:
            v=s+c
            if any(v.endswith(q) for q in forbidden):out.append(-1);continue
            target=max((q for q in prefixes if v.endswith(q)),key=len);out.append(index[target])
        edges.append(out)
    dp=[0]*len(states);dp[0]=1;counts={};A=np.zeros((len(states),len(states)))
    for i,es in enumerate(edges):
        for j in es:
            if j>=0:A[i,j]+=1
    spectral=float(np.max(np.abs(np.linalg.eigvals(A))))
    for k in range(1,129):
        nxt=[0]*len(states)
        for i,num in enumerate(dp):
            for j in edges[i]:
                if j>=0:nxt[j]+=num
        dp=nxt
        if k<=n or k in [30,40,50,64,100,128]:counts[str(k)]=sum(dp)
        if k<=n:assert sum(dp)==int(by_length[str(k)])
    out={'image_length':n,'exact_image_prefix_counts':by_length,'minimal_forbidden_words':forbidden,
         'automaton_states':len(states),'finite_type_word_counts':counts,'spectral_radius_numerical':spectral,
         'image_language_equality_proved':False,'subexponential_growth_proved':False,
         'new_obstructions_Lean_verified_only':['00','11111','010110','1011010'],
         'Lean_verified':False,'full_problem_solved':False}
    save(f'right-language-automaton-{n}.json',out)
    print({k:v for k,v in out.items() if k not in ('minimal_forbidden_words','exact_image_prefix_counts')},flush=True)

if __name__=='__main__':main()
