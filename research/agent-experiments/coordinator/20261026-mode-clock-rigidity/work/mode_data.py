from profile_data import C,integral
def states_graph(P):
    states=[(0,0,0)];index={states[0]:0};parents=[None]
    for at,(u,v,d) in enumerate(states):
        drive=u|v
        if drive.bit_count()%2==0:
            for b in range(2):
                nxt=(v,integral(drive,b,P),C[d][b])
                if nxt not in index:index[nxt]=len(states);states.append(nxt);parents.append((at,b))
        assert len(states)<1500000
    def word(i):
        w=[]
        while parents[i] is not None:i,b=parents[i];w.append(b)
        return w[::-1]
    return states,word

def rotate(x,t,P):
    t%=P;mask=(1<<P)-1
    return ((x>>t)|(x<<(P-t)))&mask

def audit(d):
    P=d['clock'];w=d['initial_parent'];field=w.copy();h=[];k=[];l=[];g=[]
    q=0
    for b in w+[0]:q=C[q][b]
    assert q in {0,1,2,3,5}
    for t in range(2*P):
        g.append(field[-1]);h.append(field[-2]);k.append(field[-3] if len(field)>=3 else 0)
        l.append(field[-4] if len(field)>=4 else 0)
        nxt=[];a=b=0
        for x in field:nxt.append((30>>(4*x+2*a+b))&1);b,a=a,x
        field=nxt
    assert field==w
    H=sum(x<<t for t,x in enumerate(h));G=sum(x<<t for t,x in enumerate(g))
    obs=G|H;mask=(1<<P)-1;mode=(G^(G>>P))&mask
    rho=(obs^(obs>>P))&mask;S=mask^(rho^rotate(rho,1,P))
    assert mode==d['mode'] and S==d['derived_observation'] and rho==d['rho']
    assert all(h[t+P]==1-h[t] for t in range(P))
    assert all(k[t+P]==k[t] for t in range(P))
    assert all(mode>>t&1 ^ (mode>>((t+1)%P)&1)==1-k[t] for t in range(P))
