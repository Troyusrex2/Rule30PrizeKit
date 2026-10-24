"""Tiny row-feature reader with time holdout and matched-top controls."""
import os
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='2'
import random
import numpy as np
from sklearn.tree import DecisionTreeClassifier,export_text
from sklearn.linear_model import LogisticRegression
from sklearn.feature_selection import SelectKBest,f_classif
from sklearn.metrics import balanced_accuracy_score
from core import phi,trace,seedlow,save,HERE

rng=random.Random(307026)
names=[]
def features(a):
    w=a.bit_length();low=(a&-a).bit_length()-1;v=a>>low
    values=[int(seedlow(v)),low]
    if not names:names.extend(['normalized_SeedLow','trailing_zeros'])
    for side,window in [('low',a&65535),('top',(a>>max(0,w-16))&65535)]:
        for k in range(1,5):
            for pat in range(1<<k):
                values.append(sum(((window>>i)&((1<<k)-1))==pat for i in range(17-k))/(17-k))
                name=f'{side}_k{k}_word{pat}'
                if len(names)<len(values):names.append(name)
    return values

def sample(start,end,matchtop):
    a=1
    for _ in range(start):a=phi(a)
    X=[];Y=[];controls=0
    for T in range(start,end):
        for P in range(8):
            pos=a<<P;w=pos.bit_length()
            high=rng.getrandbits(w-3)|(1<<(w-4))
            neg=(high<<3)|rng.choice((2,3))
            if matchtop:
                mask=((1<<16)-1)<<(w-16)
                neg=(neg&~mask)|(pos&mask)
            twin=neg^1
            # The 2/3 stripe prefix shares bit1=1, bit2=0 and all bits >=3.
            assert neg>>1==twin>>1 and neg&6==2
            if controls<8:
                assert trace(neg,1,4*w)==trace(twin,1,4*w);controls+=1
            X.extend((features(pos),features(neg)));Y.extend((1,0))
        a=phi(a)
    return np.array(X),np.array(Y),controls

def main():
    records=[]
    for matched in (False,True):
        X,y,n=sample(12,96,matched);O,yo,m=sample(96,192,matched)
        for ablated in (False,True):
            cols=[i for i,name in enumerate(names) if not ablated or name.startswith('top_')]
            for modelname in ('tree2','five-feature-logistic'):
                x=X[:,cols];o=O[:,cols]
                if modelname=='tree2':model=DecisionTreeClassifier(max_depth=2,min_samples_leaf=30,random_state=307026)
                else:
                    select=SelectKBest(f_classif,k=5).fit(x,y)
                    chosen=select.get_support(indices=True);cols=[cols[i] for i in chosen]
                    x=X[:,cols];o=O[:,cols]
                    model=LogisticRegression(C=.1,max_iter=200)
                model.fit(x,y);pred=model.predict(o)
                row={'top_matched':matched,'low_features_removed':ablated,'model':modelname,
                     'train_rows':len(y),'held_out_rows':len(yo),'train_T':[12,95],'test_T':[96,191],
                     'ood_balanced_accuracy':float(balanced_accuracy_score(yo,pred))}
                if modelname=='tree2':
                    row['selected_features']=[names[cols[i]] for i in set(model.tree_.feature) if i>=0]
                    (HERE/f'photo-tree-match{int(matched)}-ablate{int(ablated)}.txt').write_text(export_text(model,feature_names=[names[i] for i in cols]),encoding='utf-8')
                else:row['selected_features']=[names[i] for i in cols]
                records.append(row);print(row,flush=True)
    save('photo-reader.json',{'records':records,
        'negative_family':'explicit same-width stripe twins; both random-top and genuine-top-matched',
        'limitation':'This labels orbit membership, not all infinite-trace equivalence. Separating the sampled stripe grammar cannot prove canonical separation.'})

if __name__=='__main__':main()
