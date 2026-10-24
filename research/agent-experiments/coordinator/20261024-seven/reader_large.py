"""Larger width-known reader with held-out unique rows and training controls."""
import os
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='2'
import argparse,json,random,time
import numpy as np
import torch
from sklearn.ensemble import RandomForestClassifier
from sklearn.metrics import balanced_accuracy_score
from core import phi,save,HERE

def data(c,seed):
    rng=random.Random(seed);seen=set();xs=[];ys=[]
    # Split by actual row value, then shuffle; every split has equal classes.
    for split,n in [('train',40000),('validation',8000),('test',12000)]:
        X=np.empty((n,128),np.uint8);Y=np.empty(n,np.int64)
        for i in range(n):
            label=i%2
            while True:
                a=rng.getrandbits(32)|(1<<31)
                if label:a=(a|1)&~4|(((a>>1)&1)<<2)
                else:a&=~1
                if a not in seen:seen.add(a);break
            b=a
            for t in range(128):X[i,t]=(b>>(c+t))&1;b=phi(b)
            Y[i]=label
        perm=np.random.default_rng(seed+len(xs)).permutation(n)
        xs.append(X[perm]);ys.append(Y[perm])
    return xs,ys

def augment(x):
    return np.concatenate((x,x[:,:-1]^x[:,1:],x[:,:-2]^x[:,2:]),axis=1).astype(np.float32)

def metrics(model,X,Y):
    with torch.no_grad():p=model(X).argmax(1).numpy()
    return float(balanced_accuracy_score(Y,p))

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--center',type=int,required=True)
    a=parser.parse_args();c=a.center;seed=307027+c;torch.set_num_threads(2)
    torch.manual_seed(seed);start=time.monotonic()
    xs,ys=data(c,seed)
    out={'width':32,'center':c,'horizon':128,'seed':seed,'train':40000,'validation':8000,'test':12000,
         'disjoint_row_values':True,'balanced_classes_per_split':True,'models':[]}
    print({'stage':'data','seconds':round(time.monotonic()-start,3)},flush=True)
    forest=RandomForestClassifier(n_estimators=96,max_depth=14,min_samples_leaf=16,n_jobs=2,random_state=seed)
    forest.fit(augment(xs[0]),ys[0])
    out['models'].append({'model':'parity-forest','train_accuracy':float(balanced_accuracy_score(ys[0],forest.predict(augment(xs[0])))),
                         'validation_accuracy':float(balanced_accuracy_score(ys[1],forest.predict(augment(xs[1])))),
                         'test_accuracy':float(balanced_accuracy_score(ys[2],forest.predict(augment(xs[2]))))})
    print(out['models'][-1],flush=True);save(f'reader-large-c{c}.json',out)
    for mode in ('raw','local-parity'):
        arrays=[x.astype(np.float32) if mode=='raw' else augment(x) for x in xs]
        tensors=[torch.from_numpy(x) for x in arrays];y=torch.from_numpy(ys[0])
        net=torch.nn.Sequential(torch.nn.Linear(arrays[0].shape[1],128),torch.nn.ReLU(),
                                torch.nn.Linear(128,64),torch.nn.ReLU(),torch.nn.Linear(64,2))
        optimizer=torch.optim.AdamW(net.parameters(),lr=.001,weight_decay=.01)
        loss=torch.nn.CrossEntropyLoss();best=0;bestweights=None;stale=0;history=[]
        gen=torch.Generator().manual_seed(seed)
        for epoch in range(40):
            perm=torch.randperm(len(y),generator=gen)
            net.train()
            for batch in perm.split(512):
                optimizer.zero_grad();l=loss(net(tensors[0][batch]),y[batch]);l.backward();optimizer.step()
            net.eval();score=metrics(net,tensors[1],ys[1]);history.append(score)
            if score>best+.0005:
                best=score;bestweights={k:v.detach().clone() for k,v in net.state_dict().items()};stale=0
            else:stale+=1
            if stale>=8:break
        net.load_state_dict(bestweights)
        record={'model':'mlp-'+mode,'epochs':len(history),'validation_history':history,
                'train_accuracy':metrics(net,tensors[0],ys[0]),'validation_accuracy':metrics(net,tensors[1],ys[1]),
                'test_accuracy':metrics(net,tensors[2],ys[2])}
        if c==1:
            hard=xs[2][:,0]!=xs[2][:,1]
            record['hard_subset_test_accuracy']=metrics(net,tensors[2][hard],ys[2][hard])
        torch.save(net.state_dict(),HERE/f'reader-large-c{c}-{mode}.pt')
        out['models'].append(record);save(f'reader-large-c{c}.json',out);print(record,flush=True)
    out['seconds']=round(time.monotonic()-start,3);out['full_problem_solved']=False
    save(f'reader-large-c{c}.json',out);print({'stage':'complete','seconds':out['seconds']},flush=True)

if __name__=='__main__':main()
