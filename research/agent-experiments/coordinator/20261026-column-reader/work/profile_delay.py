from pathlib import Path
import json,time
ROOT=Path(__file__).resolve().parent
def integrate(g,bit,P):
    mask=(1<<P)-1;x=g;shift=1
    while shift<P:x^=x<<shift;shift*=2
    return ((x<<1)&mask)^(mask if bit else 0)
states={(0,0):0};oldP=1;records=[];start=time.monotonic()
for n in range(1,17):
    P=1<<(n-1);new={}
    for (u,v),word in states.items():
        if n>1:u=u|(u<<oldP);v=v|(v<<oldP)
        for bit in [0,1]:
            w=integrate(u|v,bit,P)
            new.setdefault((v,w),word|(bit<<(n-1)))
    states=new;oldP=P
    profiles={v:word for (_,v),word in states.items()}
    delay=0;witness=None
    while True:
        groups={};collision=None;mask=(1<<delay)-1
        for v,word in profiles.items():
            key=v&mask
            if key in groups:collision=(groups[key],(v,word));break
            groups[key]=(v,word)
        if collision is None:break
        witness=collision;delay+=1
        assert delay<=P
    if witness:
        (a,aw),(b,bw)=witness
        t=((a^b)&-(a^b)).bit_length()-1
        assert t==delay-1
        example={'a_initial':aw,'b_initial':bw,'first_difference_time':t}
    else:example=None
    rec={'initial_width':n,'pair_profile_states':len(states),'distinct_column_profiles':len(profiles),
         'time_bits_sufficient_to_distinguish_all_distinct_profiles':delay,'latest_pair':example}
    records.append(rec);print(json.dumps(rec),flush=True)
out={'records':records,'seconds':round(time.monotonic()-start,3),'finite_only':True,
     'Lean_verified':False,'uniform_delay_bound_proved':False}
(ROOT/'profile-delay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
