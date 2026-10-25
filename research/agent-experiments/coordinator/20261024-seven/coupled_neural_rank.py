"""Try a nonnegative piecewise homogeneous rank; validate before extraction.

No biases or constant feature are used, excluding a fixed finite-width
ceiling construction. A successful fit would still need exact universal
verification. Neural accuracy alone is never a proof premise.
"""
import argparse,json,random,time
import numpy as np
import torch
from core import save
from charge_beam_packed import controls
from zero_tail_block_rank import tail,six_free

def feature(st):
    w,r=st
    return [w.count(i)/128 for i in range(4)]+[
      sum(1 if j%2==0 else -1 for j,a in enumerate(w) if a==i)/128 for i in range(4)]

def main():
    p=argparse.ArgumentParser();p.add_argument('--steps',type=int,default=3000)
    p.add_argument('--seconds',type=float,default=190);a=p.parse_args();start=time.monotonic()
    torch.set_num_threads(2);torch.manual_seed(302512);rng=random.Random(302510);checked=controls()
    train=[tail(six_free(rng.randrange(16,257),rng,True),coupled_six=True,coupled_seven=True) for _ in range(700)]
    heldrng=random.Random(302513)
    held=[tail(six_free(heldrng.randrange(512,1025),heldrng,True),coupled_six=True,coupled_seven=True) for _ in range(300)]
    edges=[e for p in train for e in p];tests=[e for p in held for e in p]
    contexts=sorted({st[1] for e in edges+tests for st in e[:2]});ix={r:i for i,r in enumerate(contexts)}
    def tensors(es):
        return (torch.tensor([feature(e[0]) for e in es],dtype=torch.float64),
          torch.tensor([feature(e[1]) for e in es],dtype=torch.float64),
          torch.tensor([ix[e[0][1]] for e in es]),torch.tensor([ix[e[1][1]] for e in es]),
          torch.tensor([e[2] for e in es],dtype=torch.float64))
    X,Y,R,S,Z=tensors(edges);HX,HY,HR,HS,HZ=tensors(tests)
    W=torch.nn.Parameter(torch.randn(len(contexts),32,8,dtype=torch.float64)*.3)
    B=torch.nn.Parameter(torch.randn(len(contexts),32,dtype=torch.float64)*.1)
    optim=torch.optim.Adam([W,B],lr=.006)
    def value(x,r):return ((torch.relu(torch.einsum('bhi,bi->bh',W[r],x))*B[r]).sum(dim=1)).square()
    history=[]
    for k in range(a.steps):
        ids=torch.randint(len(edges),(min(512,len(edges)),));optim.zero_grad()
        residual=value(Y[ids],S[ids])-value(X[ids],R[ids])+Z[ids]
        loss=torch.relu(residual).square().mean()+1e-8*(W.square().mean()+B.square().mean())
        loss.backward();torch.nn.utils.clip_grad_norm_([W,B],20);optim.step()
        if (k+1)%100==0:
            with torch.no_grad():
                tr=value(Y,S)-value(X,R)+Z
                rec={'step':k+1,'training_max_residual':float(tr.max()),'training_violations':int((tr>1e-5).sum()),
                    'seconds':round(time.monotonic()-start,3)};history.append(rec)
                if (k+1)%500==0:print(rec,flush=True)
                if tr.max()<1e-5 or time.monotonic()-start>a.seconds:break
    with torch.no_grad():
        tr=value(Y,S)-value(X,R)+Z;hr=value(HY,HS)-value(HX,HR)+HZ
    out={'rank':'square of bias-free state-conditioned ReLU readout','features':'letter and signed position-parity counts',
         'training_edges':len(edges),'heldout_edges':len(tests),'training_widths':[16,256],'heldout_widths':[512,1024],
         'heldout_seed':302513,'contexts':len(contexts),'training_max_residual':float(tr.max()),
         'training_violations':int((tr>1e-5).sum()),'heldout_max_residual':float(hr.max()),
         'heldout_violations':int((hr>1e-5).sum()),'history':history,'controls':checked,
         'nonnegative_by_construction':True,'has_constant_or_bias':False,
         'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
    if out['training_violations']==0 and out['heldout_violations']==0:
        out['provisional_weights']={'contexts':contexts,'W':W.detach().tolist(),'readout':B.detach().tolist()}
    save('coupled-neural-rank.json',out);print({k:v for k,v in out.items() if k not in ('history','provisional_weights','controls')},flush=True)

if __name__=='__main__':main()
