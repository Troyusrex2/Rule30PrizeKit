"""Analyze cycles in the finite-window overapproximation, not the true image.

A branching strongly connected component obstructs an argument that this
finite guard alone forces every infinite word to become periodic.
"""
import argparse,json
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from scipy.sparse.linalg import eigs
from core import HERE,save

def main():
    p=argparse.ArgumentParser();p.add_argument('--window',type=int,default=30);a=p.parse_args()
    r=json.loads((HERE/f'right-image-smt-{a.window}.json').read_text(encoding='utf-8'))
    assert r['finite_census_complete'];W=a.window;mask=(1<<(W-1))-1
    words={int(w) for w in r['image_witnesses']};vertices=sorted({w&mask for w in words}|{w>>1 for w in words});ix={v:i for i,v in enumerate(vertices)}
    edges=[(ix[w&mask],ix[w>>1],w>>(W-1)) for w in sorted(words)]
    A=coo_matrix((np.ones(len(edges)),([e[0] for e in edges],[e[1] for e in edges])),shape=(len(vertices),len(vertices))).tocsr()
    nscc,labels=connected_components(A,directed=True,connection='strong');sizes=np.bincount(labels);internal=[[] for _ in vertices]
    for i,j,b in edges:
        if labels[i]==labels[j]:internal[i].append((j,b))
    branch=[i for i,es in enumerate(internal) if len(es)>1];components=[]
    for c in np.argsort(sizes)[::-1][:10]:
        vs=np.where(labels==c)[0];components.append({'vertices':int(len(vs)),'internal_edges':sum(len(internal[i]) for i in vs),
            'branching_vertices':sum(len(internal[i])>1 for i in vs)})
    spectral=float(abs(eigs(A,k=1,which='LM',return_eigenvectors=False,maxiter=20000,tol=1e-10)[0]))
    out={'window':W,'vertices':len(vertices),'edges':len(edges),'strong_components':int(nscc),
        'largest_components':components,'branching_vertices_in_strong_components':len(branch),
        'example_branching_window':None if not branch else format(vertices[branch[0]],f'0{W-1}b')[::-1],
        'spectral_radius_numerical':spectral,
        'finite_guard_forces_all_streams_eventually_periodic':not bool(branch),
        'true_image_identified_with_guard':False,'Lean_verified':False,'full_problem_solved':False}
    save(f'right-image-graph-{W}.json',out);print(out,flush=True)

if __name__=='__main__':main()
