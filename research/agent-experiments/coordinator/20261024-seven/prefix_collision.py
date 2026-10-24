"""Exact finite-width class-prefix collision search, without infinite claims."""
from core import phi,seedlow,save
import time

def main():
    start=time.monotonic();out=[]
    for w in range(4,15):
        centers=sorted({1,w//2,w-1});H=4*w
        buckets=[{} for _ in centers]
        first=[None]*len(centers);counts=[0]*len(centers)
        for a in range(1<<(w-1),1<<w):
            if a&1 and not seedlow(a):continue
            label=int(bool(a&1));keys=[0]*len(centers);b=a
            for t in range(H):
                for i,c in enumerate(centers):keys[i]|=((b>>(c+t))&1)<<t
                b=phi(b)
            for i,key in enumerate(keys):
                old=buckets[i].get(key)
                if old is not None and (old&1)!=label:
                    counts[i]+=1
                    if first[i] is None:first[i]=(old,a)
                else:buckets[i][key]=a
        for i,c in enumerate(centers):
            item={'width':w,'center':c,'horizon':H,'cross_class_collisions':counts[i],'first':first[i]}
            if first[i]:
                a,b=first[i];diff=None
                for t in range(4096):
                    if ((a^b)>>(c+t))&1:diff=t;break
                    a=phi(a);b=phi(b)
                item['first_difference_before_4096']=diff
            out.append(item)
        print({'width':w,'collisions':counts,'seconds':round(time.monotonic()-start,3)},flush=True)
        save('prefix-collision-progress.json',out)
    save('prefix-collision.json',{'records':out,'seconds':round(time.monotonic()-start,3),
         'limitation':'Completed finite domains only; no infinite separation or uniform horizon proof.'})

if __name__=='__main__':main()
