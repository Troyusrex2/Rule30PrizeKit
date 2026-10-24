"""Expose local parity features so known XOR signals are learnable."""
import os
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='2'
import numpy as np
from sklearn.linear_model import LogisticRegression
from sklearn.tree import DecisionTreeClassifier, export_text
from sklearn.metrics import balanced_accuracy_score
from core import HERE, save

def features(x):
    return np.concatenate([x,*(x[:,:-d]^x[:,d:] for d in (1,2,3,4)),
                           x[:,:-2]^x[:,1:-1]^x[:,2:]],axis=1)

def main():
    d=np.load(HERE/'reader-data.npz');out=[]
    for ci,c in enumerate((1,4,8)):
        X=features(d['train'][:,ci]);I=features(d['iid'][:,ci]);O=features(d['ood'][:,ci])
        for name,model in [('sparse-parity-logistic',LogisticRegression(C=.05,l1_ratio=1,solver='liblinear',max_iter=300,random_state=307024)),
                           ('parity-tree',DecisionTreeClassifier(max_depth=5,min_samples_leaf=50,random_state=307024))]:
            model.fit(X,d['y'])
            row={'center':c,'model':name}
            for split,x in [('iid',I),('ood',O)]:
                y=d['yi'] if split=='iid' else d['yo'];p=model.predict(x)
                raw=d[split][:,ci];hard=raw[:,0]!=raw[:,1]
                row[split]={'balanced_accuracy':float(balanced_accuracy_score(y,p)),
                            'hard_subset_balanced_accuracy':float(balanced_accuracy_score(y[hard],p[hard]))}
            if hasattr(model,'coef_'):
                row['nonzero_features']=[(int(i),float(model.coef_[0,i])) for i in np.flatnonzero(model.coef_[0])]
            else:(HERE/f'reader-parity-tree-c{c}.txt').write_text(export_text(model),encoding='utf-8')
            out.append(row);print(row,flush=True)
    save('reader-features.json',out)

if __name__=='__main__':main()
