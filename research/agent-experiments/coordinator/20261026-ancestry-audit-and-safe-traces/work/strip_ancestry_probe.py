"""Test arbitrary-clock left extensions of genuine plateau candidates.

A finite product graph tracks time modulo P and all strip cells. Its two
oldest cells are free at every tick; a directed cycle is equivalent to an
infinite extension in this relaxation. Older periods need not divide P.
"""
from pathlib import Path
import json,time
from profile_data import integral
from mode_data import rotate
r=Path(__file__).resolve().parent;start=time.monotonic()
R=8;P=2*R;mask=(1<<P)-1;small=(1<<R)-1
candidates=[]
for K in range(1<<R):
    k=K|((small^K)<<R);dk=k^rotate(k,1,P)
    for L in range(1<<R):
        if L.bit_count()%2==0:continue
        l=L|(L<<R);dl=l^rotate(l,1,P)
        if l&~dk or (dk&~l&~dl&mask):continue
        H=integral((k|l)|((k|l)<<P),0,2*P)
        G=integral(H|(k|(k<<P)),0,2*P);q=(G^(G>>P))&mask
        S=q|(~k&~l&mask)
        H1=H^((1<<(2*P))-1)
        G1=integral(H1|(k|(k<<P)),0,2*P)
        assert ((G1^(G1>>P))&mask)==q
        candidates.append({'k':k,'l':l,'g':G,'h':H,'q':q,'S':S})

def cycle(item,width,save=False):
    N=1<<(width-2);wmask=(1<<width)-1
    forced=[((item['k']>>t&1)<<1)|(item['l']>>t&1) for t in range(P)]
    colors=bytearray(P*N);position={};tested=0
    def successors(v):
        phase,low=divmod(v,N);w=low|(forced[phase]<<(width-2))
        high=(w^((w<<1)|(w<<2)))&wmask&~3;phase2=(phase+1)%P
        if high>>(width-2)!=forced[phase2]:return ()
        base=phase2*N+(high&(N-1))
        return (base,base|1,base|2,base|3)
    for init in range(N):
        if colors[init]:continue
        stack=[(init,0,successors(init))];colors[init]=1;position[init]=0
        while stack:
            v,i,ys=stack[-1]
            if i==len(ys):colors[v]=2;position.pop(v);stack.pop();continue
            y=ys[i];stack[-1]=(v,i+1,ys)
            if colors[y]==1:
                if not save:return True,None
                walk=[x[0] for x in stack[position[y]:]]
                at=next(i for i,v in enumerate(walk) if v//N==0)
                walk=walk[at:]+walk[:at]
                words=[v%N|(forced[v//N]<<(width-2)) for v in walk]
                assert len(words)%P==0
                for t,a in enumerate(words):
                    b=words[(t+1)%len(words)]
                    assert a>>(width-2)==forced[t%P]
                    for j in range(2,width):
                        assert (b>>j&1)==((30>>(4*(a>>j&1)+2*(a>>(j-1)&1)+(a>>(j-2)&1)))&1)
                return True,{'width':width,'period':len(words),'states_phase_zero_start':words,
                             'oldest_two_inputs_free':True,'older_period_may_exceed_P':True}
            if colors[y]==0:
                colors[y]=1;position[y]=len(stack);stack.append((y,0,successors(y)))
    return False,None

reports=[];survivors=list(range(len(candidates)))
for width in [4,5,6,8,10,12]:
    t0=time.monotonic();survivors=[i for i in survivors if cycle(candidates[i],width)[0]]
    seen={};collision=None
    for i in survivors:
        x=candidates[i]
        if x['S'] in seen and candidates[seen[x['S']]]['q']!=x['q']:
            collision=[seen[x['S']],i];break
        seen.setdefault(x['S'],i)
    witness=None
    if collision:
        witness=[]
        for i in collision:
            ok,walk=cycle(candidates[i],width,True);assert ok
            witness.append({'candidate':candidates[i],'older_extension':walk})
    report={'older_strip_width_ending_at_k':width,'surviving_pairs':len(survivors),
            'mode_collision':witness,'seconds':round(time.monotonic()-t0,3)}
    reports.append(report)
    print(json.dumps({k:v for k,v in report.items() if k!='mode_collision'}|{'collision_found':collision is not None}),flush=True)
    (r/'strip-ancestry-probe.json').write_text(json.dumps({'R':R,'clock':P,'candidate_pairs':len(candidates),
      'reports':reports,'older_periods_not_forced_to_divide_P':True,'both_h_phases_checked':True,
      'finite_white_ancestry_established':False,'Lean_verified':False,
      'uniform_mode_inverse_proved':False,'full_problem_solved':False,
      'seconds':round(time.monotonic()-start,3)},indent=2)+'\n')
    if collision is None:break
