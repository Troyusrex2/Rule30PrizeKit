from pathlib import Path
import hashlib,json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
root=Path(__file__).resolve().parent
T=24;lo=-18;hi=20;origin=90;L=183;mask=(1<<L)-1
a=sum(1<<p for p in range(L) if (p-origin)%3==1)
b=sum(1<<p for p in range(L) if (p-origin)%3==2)
h=sum(1<<(origin+p) for p in [-5,-4,4,5]);c=a^h
def F(v):return ((v<<1)^(v|(v>>1)))&mask
hs=[];actual=[]
for t in range(T+1):
    hs.append([(h>>(origin+p))&1 for p in range(lo,hi+1)])
    actual.append([((c^a)>>(origin+p))&1 for p in range(lo,hi+1)])
    a,b,h,c=F(a),F(b),((h<<1)^(h&~(b>>1))^((h>>1)&~a))&mask,F(c)
assert all(row[1-lo]==0 for row in hs)
assert all(actual[t][1-lo]==0 for t in range(7)) and actual[7][1-lo]==1
assert hs[:4]==actual[:4] and hs[4][-5-lo]!=actual[4][-5-lo]
fig,axes=plt.subplots(1,2,figsize=(10.4,4.7),sharey=True)
for ax,data,title in zip(axes,[hs,actual],['Auxiliary linear mode h','Actual physical difference C XOR A']):
    ax.imshow(np.array(data),cmap='binary',vmin=0,vmax=1,interpolation='nearest',
              extent=(lo-.5,hi+.5,T+.5,-.5),aspect='equal')
    ax.axvline(1,color='#c0392b',linewidth=.85,alpha=.8)
    ax.set_title(title,fontsize=11,pad=9);ax.set_xlabel('Position p')
    ax.set_xticks([-15,-10,-5,1,5,10,15,20]);ax.set_yticks([0,4,8,12,16,20,24])
axes[0].set_ylabel('Time t')
fig.suptitle('Periodic-background control: a gauge-invariant mode need not be physical',fontsize=12,y=.97)
fig.text(.5,.035,'Red line: observation column p=1. The auxiliary trace stays white; the physical trace first differs at t=7.\nThese infinite initial backgrounds are not the canonical single-seed case.',ha='center',fontsize=9)
fig.subplots_adjust(top=.88,bottom=.19,left=.07,right=.98,wspace=.12)
path=root/'observer-barrier.png';fig.savefig(path,dpi=160,facecolor='white');plt.close(fig)
out={'pass':True,'auxiliary':hs,'physical_difference':actual,'positions':[lo,hi],
     'times':[0,T],'observation_column':1,'first_physical_center_difference':7,
     'first_physicality_failure':[4,-5],'figure_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
     'scope':'Infinite periodic backgrounds; not a canonical or finite-background counterexample.'}
(root/'observer-preview.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['auxiliary','physical_difference']}))
