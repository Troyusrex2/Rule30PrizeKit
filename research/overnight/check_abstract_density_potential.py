"""Check candidate potentials on a regular overapproximation of reachable ribbons.

Old diagonals A,B satisfy B_i <= A_i xor A_(i+1) <= B_i OR B_(i-1).
The next diagonal C obeys C_i xor C_(i+1)=A_i OR B_(i-1).
Dynamic programming retains the last radius-1 bits of A,B,C, so its state
space is independent of word length. A counterexample here rejects a proof
using this ribbon abstraction; it need NOT be reachable from a legal gate.
No numerical graph result is promoted to a Lean theorem.
"""
import argparse
import json
from pathlib import Path

from reachable_variation_potential import advance, features


def reverse_bits(n,width):
    return int(f'{n:0{width}b}'[::-1],2)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('candidate',type=Path)
    ap.add_argument('--max-width',type=int,default=128)
    ap.add_argument('--min-width',type=int)
    ap.add_argument('--head-history',type=int,default=0,
                    help='Constrain the ribbon head by this many legal boundary observations')
    args=ap.parse_args()
    model=json.loads(args.candidate.read_text(encoding='utf-8'))
    assert model['exact_three_or_five'] and not model.get('output_charge_by_depth',False)
    assert model.get('temporal_clock',2)==2 and model.get('spatial_period',1)==1
    r=model['radius'];weights=model['weights'];C=model['coefficient']
    assert r>=2
    patterns=1 << (2*r-1);span=6*patterns;bulk=model.get('bulk_weights_depend_on_controller',False)
    headbase=span*(5 if bulk else 1);small=(1 << (r-1))-1;full=(1 << r)-1
    rev=[reverse_bits(n,r) for n in range(1 << r)]
    revsmall=[reverse_bits(n,r-1) for n in range(1 << (r-1))]
    def coefficient(age,phase,group,code):
        return weights[(age*span if bulk else 0)+phase*3*patterns+group*patterns+code]
    def potential(a,b,k,age):
        f=features(a,b,k,r)
        return sum(v*weights[j+(age*span if bulk else 0)] for j,v in f.items())+weights[headbase+(k%2)*5+age]
    def prefixes(k,age):
        length=args.head_history
        if not length:return None
        states={(0,0,oldage) for oldage in range(5)}
        for i in range(length):
            nxt=set();phase=(k-length+i)%2
            for a,b,oldage in states:
                heads=[1] if phase else [0] if oldage==4 else [0,1] if oldage==2 else [1]
                for head in heads:
                    na=(0 if head==0 else min(4,oldage+1)) if phase==0 else oldage
                    c=advance(a,b,i,head);nxt.add((c,a,na))
            states=nxt
        return [(a,b) for a,b,na in sorted(states) if na==age]
    def test(k,age,head):
        phase=k%2;nextage=(0 if head==0 else min(4,age+1)) if phase==0 else age
        a0=1 if phase==0 or age>0 else 0
        b0=1 if phase==1 or age>0 else 0
        reward=int(phase==0)
        initial=weights[headbase+(1-phase)*5+nextage]-weights[headbase+phase*5+age]+reward
        # (A suffix,B suffix,C suffix) -> (score,wholeA,wholeB)
        pref=prefixes(k,age)
        if pref==[]:return None
        initialmask=1 if pref is None else (1<<len(pref))-1
        am=[];bm=[]
        if pref is not None:
            for i in range(args.head_history):
                am.append([sum(1<<j for j,(a,b) in enumerate(pref) if (a>>i)&1==x) for x in [0,1]])
                bm.append([sum(1<<j for j,(a,b) in enumerate(pref) if (b>>i)&1==x) for x in [0,1]])
        states={(0,0,head,initialmask):(initial,0,0)}
        for i in range(k):
            nxt={}
            for (ab,bb,cb,pm),(score,a,b) in states.items():
                for ai in ([a0] if i==0 else [0,1]):
                    pa=pm & am[i][ai] if pref is not None and i<args.head_history else pm
                    if pa==0:continue
                    if i:
                        derivative=(ab&1)^ai;bp=bb&1;bpp=(bb>>1)&1 if i>1 else 0
                        if bp>derivative or derivative>(bp|bpp):continue
                    ci=(cb&1)^(ai|((bb&1) if i else 0))
                    af=((ab<<1)|ai)&full;cf=((cb<<1)|ci)&full
                    change=0.0
                    if i>=r-1:
                        oldcode=rev[af]|(revsmall[bb&small]<<r)
                        change-=coefficient(age,phase,0,oldcode)
                        if i==r-1:change-=coefficient(age,phase,1,oldcode)
                        if i==k-1:change-=coefficient(age,phase,2,oldcode)
                    if i>=r-2:
                        newcode=rev[cf]|(revsmall[af&small]<<r)
                        change+=coefficient(nextage,1-phase,0,newcode)
                        if i==r-2:change+=coefficient(nextage,1-phase,1,newcode)
                        if i==k-1:change+=coefficient(nextage,1-phase,2,newcode)
                    for bi in ([0] if i==k-1 else [b0] if i==0 else [0,1]):
                        pb=pa & bm[i][bi] if pref is not None and i<args.head_history-1 else pa
                        if pb==0:continue
                        if pref is not None and i>=args.head_history-1:pb=1
                        key=(af&small,((bb<<1)|bi)&small,cf&small,pb)
                        value=score+change
                        if key not in nxt or value>nxt[key][0]:
                            nxt[key]=(value,a|(ai<<i),b|(bi<<i))
            states=nxt
        if not states:return None
        key,(score,a,b)=max(states.items(),key=lambda item:item[1][0]-C*(item[0][2]&1))
        c=advance(a,b,k,head)
        direct=potential(c,a,k+1,nextage)-potential(a,b,k,age)+reward-C*((c>>k)&1)
        residual=score-C*(key[2]&1)
        assert abs(direct-residual)<1e-6,(direct,residual)
        assert (c>>k)&1==key[2]&1
        return {'width':k,'age':age,'head':head,'residual':direct,'A':a,'B':b,
                'next_diagonal':c,'DP_states':len(states),'reached_from_gate_proved':False}
    report={'finite_width_check_only':True,'unbounded_potential_proved':False,
            'ribbon_overapproximation':True,'candidate':args.candidate.name,'counterexample':None,
            'legal_head_history_length':args.head_history}
    tests=0
    for k in range(max(r,args.head_history,args.min_width or r),args.max_width+1):
        for age in range(5):
            heads=[1] if k%2 else [0] if age==4 else [0,1] if age==2 else [1]
            for head in heads:
                got=test(k,age,head);tests+=1
                if got and got['residual']>1e-6:
                    report['counterexample']=got;break
            if report['counterexample']:break
        if report['counterexample']:break
    report['tests']=tests
    suffix=f'-head{args.head_history}' if args.head_history else ''
    if args.min_width:suffix+=f'-from{args.min_width}'
    target=args.candidate.with_name(args.candidate.stem+'-abstract-check'+suffix+'.json')
    target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__':main()
