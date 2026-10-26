C=[[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]]
D={0,1,4,5}
def integral(x,b,P):
    y=x;s=1;mask=(1<<P)-1
    while s<P:y^=y<<s;s*=2
    return ((y<<1)&mask)^(mask if b else 0)

def graph(P):
    states=[(0,0,0)];index={states[0]:0};parents=[None];chosen={}
    for at,(u,v,d) in enumerate(states):
        drive=u|v
        if d in D:
            if drive not in chosen:chosen[drive]=at
            else:assert states[chosen[drive]][1]==v
        if drive.bit_count()%2==0:
            for b in range(2):
                nxt=(v,integral(drive,b,P),C[d][b])
                if nxt not in index:index[nxt]=len(states);states.append(nxt);parents.append((at,b))
        assert len(states)<1500000
    def word(i):
        out=[]
        while parents[i] is not None:i,b=parents[i];out.append(b)
        return out[::-1]
    data=[]
    for profile,i in chosen.items():
        data.append({'clock':P,'OR_profile':profile,'target':states[i][1]&1,'parent_initial':word(i)})
    return data,len(states)

def literal(data):
    P=data['clock'];state=data['parent_initial'].copy();g=[];rr=[]
    for t in range(P):
        g.append(state[-1] if state else 0)
        rr.append((state[-1] if state else 0)|(state[-2] if len(state)>1 else 0))
        nxt=[];a=b=0
        for x in state:nxt.append((30>>(4*x+2*a+b))&1);b,a=a,x
        state=nxt
    assert state==data['parent_initial']
    assert sum(v<<i for i,v in enumerate(rr))==data['OR_profile'] and g[0]==data['target']
