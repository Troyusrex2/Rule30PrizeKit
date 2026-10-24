"""Reproducible, fixed-frame trace reader pilot. No accuracy is a proof."""
import os
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[k]='2'
import json, random, time
import numpy as np
from sklearn.linear_model import LogisticRegression
from sklearn.tree import DecisionTreeClassifier, export_text
from sklearn.ensemble import RandomForestClassifier
from sklearn.neural_network import MLPClassifier
from sklearn.metrics import balanced_accuracy_score, accuracy_score
from core import phi, seedlow, trace, controls, save, HERE

SEED=307024; H=256; CENTERS=(1,4,8)
rng=random.Random(SEED); used=set()

def sample(widths,n):
    data=[];labels=[];width=[]
    for w in widths:
        for label in (0,1):
            count=0
            while count<n:
                a=rng.getrandbits(w)|(1<<(w-1))
                if label:
                    a|=1
                    a=(a&~4)|(((a>>1)&1)<<2)
                else:a&=~1
                if a in used:continue
                assert a.bit_length()==w and seedlow(a)==bool(label)
                used.add(a);count+=1
                features=np.empty((len(CENTERS),H),dtype=np.uint8)
                b=a
                for t in range(H):
                    for ci,c in enumerate(CENTERS):features[ci,t]=(b>>(c+t))&1
                    b=phi(b)
                data.append(features);labels.append(label);width.append(w)
    return np.asarray(data),np.asarray(labels),np.asarray(width)

def metrics(y,p,x):
    hard=x[:,0]!=x[:,1]
    return {'accuracy':float(accuracy_score(y,p)),
            'balanced_accuracy':float(balanced_accuracy_score(y,p)),
            'rows':len(y),'hard_subset_rows':int(hard.sum()),
            'hard_subset_balanced_accuracy':float(balanced_accuracy_score(y[hard],p[hard]))}

def main():
    started=time.monotonic()
    out={'seed':SEED,'horizon':H,'centers':CENTERS,'controls':controls(),
         'input':'trace bits only; separate fixed-center models',
         'training_widths':[16,20,24,28],'ood_widths':[32,48,64],
         'interpretation':'finite-sample classifier only; not a separation proof', 'models':[]}
    train,y,wt=sample([16,20,24,28],750)
    iid,yi,wi=sample([16,20,24,28],200)
    ood,yo,wo=sample([32,48,64],300)
    print(json.dumps({'stage':'data','train':len(y),'iid':len(yi),'ood':len(yo)}),flush=True)
    np.savez_compressed(HERE/'reader-data.npz',train=train,y=y,wt=wt,iid=iid,yi=yi,wi=wi,ood=ood,yo=yo,wo=wo)
    for ci,c in enumerate(CENTERS):
        x=train[:,ci,:]
        models=[('logistic',LogisticRegression(max_iter=150,C=.1,random_state=SEED)),
                ('tree6',DecisionTreeClassifier(max_depth=6,min_samples_leaf=40,random_state=SEED)),
                ('forest',RandomForestClassifier(n_estimators=48,max_depth=10,min_samples_leaf=12,n_jobs=2,random_state=SEED)),
                ('mlp',MLPClassifier(hidden_layer_sizes=(32,16),max_iter=60,early_stopping=True,random_state=SEED))]
        for name,model in models:
            before=time.monotonic();model.fit(x,y)
            row={'center':c,'model':name,'seconds':round(time.monotonic()-before,3),
                 'iid':metrics(yi,model.predict(iid[:,ci,:]),iid[:,ci,:]),
                 'ood':metrics(yo,model.predict(ood[:,ci,:]),ood[:,ci,:])}
            if hasattr(model,'feature_importances_'):
                ix=np.argsort(model.feature_importances_)[-12:][::-1]
                row['trace_time_importances']=[(int(k),float(model.feature_importances_[k])) for k in ix]
            if name=='tree6':(HERE/f'reader-tree-c{c}.txt').write_text(export_text(model),encoding='utf-8')
            out['models'].append(row);save('reader.json',out);print(json.dumps(row),flush=True)
        # Full negative control using a shuffled training label vector.
        shuffled=np.random.default_rng(SEED).permutation(y)
        control=LogisticRegression(max_iter=150,C=.1,random_state=SEED).fit(x,shuffled)
        out['models'].append({'center':c,'model':'shuffled-label-logistic',
            'iid':metrics(yi,control.predict(iid[:,ci,:]),iid[:,ci,:]),
            'ood':metrics(yo,control.predict(ood[:,ci,:]),ood[:,ci,:])})
        # Known first-two-bit discriminator, not a new result.
        out['models'].append({'center':c,'model':'known-two-bit-baseline',
            'iid':metrics(yi,(iid[:,ci,0]!=iid[:,ci,1]).astype(int),iid[:,ci,:]),
            'ood':metrics(yo,(ood[:,ci,0]!=ood[:,ci,1]).astype(int),ood[:,ci,:])})
    out['seconds']=round(time.monotonic()-started,3)
    save('reader.json',out)
    print(json.dumps({'stage':'complete','seconds':out['seconds']}),flush=True)

if __name__=='__main__':main()
