"""Exact adaptive maximum cross-class delay on finite same-width domains."""
import argparse,time
from core import phi,seedlow,trace,save

def domain(w,c,horizon=2048):
    # Every group stores current rows, initial rows, and labels. Mixed groups
    # alone can still contribute to the maximum cross-class common prefix.
    group=[(a,a,int(bool(a&1))) for a in range(1<<(w-1),1<<w) if a&1==0 or seedlow(a)]
    total=len(group);groups=[group];last=None;states=0;start=time.monotonic()
    for t in range(horizon):
        new=[]
        for group in groups:
            left=[];right=[];flags=[0,0]
            for current,initial,label in group:
                bit=(current>>(c+t))&1
                (right if bit else left).append((current,initial,label))
                flags[bit]|=1<<label;states+=1
            for bit,bucket in enumerate((left,right)):
                if flags[bit]==3:
                    new.append([(phi(current),initial,label) for current,initial,label in bucket])
        if not new:
            a=next(x[1] for x in groups[0] if x[2]==0)
            b=next(x[1] for x in groups[0] if x[2]==1)
            delta=trace(a,c,t+1)^trace(b,c,t+1)
            assert delta==1<<t
            return {'width':w,'center':c,'rows':total,'completed':True,
                    'longest_cross_class_common_prefix':t,'maximal_delay_witness':[a,b],
                    'both_same_exact_width':True,'states_processed':states,
                    'seconds':round(time.monotonic()-start,3)}
        groups=new
    a=next(x[1] for x in groups[0] if x[2]==0);b=next(x[1] for x in groups[0] if x[2]==1)
    return {'width':w,'center':c,'rows':total,'completed':False,
            'unresolved_prefix_collision':[a,b],'horizon':horizon,
            'seconds':round(time.monotonic()-start,3)}

def controls():
    pairs=0
    for w in range(4,9):
        for c in (1,w//2,w-1):
            A=range(1<<(w-1),1<<w,2)
            B=[a for a in range((1<<(w-1))+1,1<<w,2) if seedlow(a)]
            ta={a:trace(a,c,512) for a in A};tb={a:trace(a,c,512) for a in B}
            longest=-1
            for a in A:
                for b in B:
                    d=ta[a]^tb[b];assert d
                    longest=max(longest,(d&-d).bit_length()-1);pairs+=1
            result=domain(w,c)
            assert result['completed'] and result['longest_cross_class_common_prefix']==longest
    return {'bruteforce_pairs':pairs,'all_passed':True}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--widths',type=int,nargs='+',default=[10,12,14,16,18,20])
    args=parser.parse_args();out={'controls':controls(),'records':[],
        'all_time_class_separation_proved':False,'full_problem_solved':False}
    for w in args.widths:
        for c in (1,w//2,w-1):
            r=domain(w,c);out['records'].append(r);save('class-horizon.json',out);print(r,flush=True)
            if not r['completed']:return

if __name__=='__main__':main()
