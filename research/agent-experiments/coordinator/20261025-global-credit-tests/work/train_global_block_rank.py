"""Numerical discovery of a whole-multiset rank; exact integer validation follows.
No causal parent inequalities and no held-out tuning are used. The candidate
family remains alpha(type)*run_length+beta(type), with nonnegative coefficients.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib,json,sys,time
import numpy as np
import torch
from torch import nn
import torch.nn.functional as F
root=Path(__file__).resolve().parent
started=time.monotonic();N=4096;P=16;seed=30302519
np.random.seed(seed);torch.manual_seed(seed);torch.set_num_threads(2)
assert torch.cuda.is_available();device=torch.device('cuda')
assert torch.cuda.mem_get_info()[0]>2*1024**3
def phi(a):return a^((a<<1)|(a<<2))
def runs(d):
    while d:
        lo=(d&-d).bit_length()-1;n=((d>>lo)^((d>>lo)+1)).bit_length()-1
        yield lo,lo+n-1;d&=~(((1<<n)-1)<<lo)
types=list(product(range(16),[0,3],[1,2],[1,2],[0,3]));ids={v:i for i,v in enumerate(types)}
def feature(a,b,lo,hi,phase):
    def pair(i):return ((a>>i)&1)|(((b>>i)&1)<<1) if i>=0 else 0
    return ids[(phase,pair(lo-1),pair(lo),pair(hi),pair(hi+1))],hi-lo+1
rows=[1]
for _ in range(N+P+2):rows.append(phi(rows[-1]))
records=[]
for n in range(N):
    if not all((rows[n+i]>>(n+i)&1)==(rows[n+P+i]>>(n+P+i)&1) for i in range(3)):continue
    a,b=rows[n]<<P,rows[n+P];an,bn=rows[n+2]<<P,rows[n+P+2]
    old=Counter(feature(a,b,l,h,n%16) for l,h in runs(a^b))
    new=Counter(feature(an,bn,l,h,(n+2)%16) for l,h in runs(an^bn))
    delta=old.copy();delta.subtract(new)
    records.append({'onset':n,'old':old,'new':new,'delta':[(t,l,c) for (t,l),c in delta.items() if c]})
training=[r for r in records if r['onset']<1024];held=[r for r in records if r['onset']>=1024]
assert not {r['onset'] for r in training}&{r['onset'] for r in held}
width=max(len(r['delta']) for r in training)
t=np.zeros((len(training),width),dtype=np.int64);length=np.zeros_like(t,dtype=np.float32)
logplus=np.full_like(length,-1e8);logminus=np.full_like(length,-1e8)
for i,r in enumerate(training):
    for j,(ty,le,c) in enumerate(r['delta']):
        t[i,j]=ty;length[i,j]=le
        (logplus if c>0 else logminus)[i,j]=np.log(abs(c))
T=torch.tensor(t,device=device);L=torch.tensor(length,device=device)
LP=torch.tensor(logplus,device=device);LM=torch.tensor(logminus,device=device)
raw=nn.Parameter(torch.randn(2,len(types),device=device)*.15-1.5)
opt=torch.optim.Adam([raw],lr=.025)
def exact(weights,part):
    alpha,beta=weights;bad=[]
    for r in part:
        d=Counter()
        for (ty,le),count in r['old'].items():d[int(alpha[ty])*le+int(beta[ty])]+=count
        for (ty,le),count in r['new'].items():d[int(alpha[ty])*le+int(beta[ty])]-=count
        nonzero=[(k,v) for k,v in d.items() if v]
        count_answer=bool(nonzero) and max(nonzero)[1]>0
        old=[int(alpha[ty])*le+int(beta[ty]) for (ty,le),c in r['old'].items() for _ in range(c)]
        new=[int(alpha[ty])*le+int(beta[ty]) for (ty,le),c in r['new'].items() for _ in range(c)]
        assert count_answer==(sorted(new,reverse=True)<sorted(old,reverse=True))
        if not count_answer:bad.append(r['onset'])
    return bad
fitstart=time.monotonic();best=None;history=[];step=0
while step<20000 and time.monotonic()-fitstart<105:
    tau=3+47*min(step/8000,1)
    positive=F.softplus(raw);score=positive[0,T]*L+positive[1,T]
    lhs=torch.logsumexp(tau*score+LP,dim=1);rhs=torch.logsumexp(tau*score+LM,dim=1)
    loss=F.softplus(rhs-lhs+.25).mean()/tau+1e-5*positive.square().mean()
    opt.zero_grad();loss.backward();torch.nn.utils.clip_grad_norm_([raw],5);opt.step();step+=1
    if step%500==0:
        c=F.softplus(raw).detach().cpu().numpy()
        choices=[]
        for scale in [1,8,64,512,4096]:
            w=np.rint(c*scale).astype(np.int64);bad=exact(w,training);choices.append((len(bad),scale,w,bad))
        selected=min(choices,key=lambda v:(v[0],v[1]));key=selected[:2]
        if best is None or key<best[0]:best=(key,selected[2].copy(),selected[3],step,float(loss.item()))
        history.append({'step':step,'loss':float(loss.item()),'training_integer_failures':selected[0],'scale':selected[1]})
        if step%2000==0:print(json.dumps(history[-1]),flush=True)
assert best is not None
key,w,trainbad,beststep,bestloss=best
heldbad=exact(w,held)
out={'finite_only':True,'Lean_verified':False,'seed':seed,'torch':torch.__version__,
     'device':torch.cuda.get_device_name(0),'distinct_onsets':N,'lag':P,'training_unique_guarded':len(training),'heldout_unique_guarded':len(held),
     'training_range':[0,1024],'heldout_range':[1024,4096],'steps':step,'best_training_step':beststep,
     'best_training_loss':bestloss,'quantization_scale':key[1],
     'training_exact_failure_onsets':trainbad,'heldout_exact_failure_onsets':heldbad,
     'weights':[{'type':ty,'alpha':int(w[0,i]),'beta':int(w[1,i])} for i,ty in enumerate(types)],
     'history':history,'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'Smooth discovery objective approximates ordinal comparison; final validation uses exact nonnegative integer ranks and two equivalent global multiset algorithms. Model/scale selection uses training only. No held-out failures were used to tune or refit. No uniform claim.'}
(root/'trained-global-block-rank.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'steps':step,'training_failures':len(trainbad),'heldout_failures':len(heldbad),'seconds':out['seconds']}),flush=True)
