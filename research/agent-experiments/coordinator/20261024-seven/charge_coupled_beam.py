"""Falsify counting bounds after strengthening the coupled boundary language.

Failure to find a counterexample is not a theorem. Numerical full image
constraints beyond the six-word theorem are labeled separately.
"""
import argparse,json,time
from core import HERE,save
from charge_beam_packed import step,controls,check_full
from even_code_charge import words

def main():
    p=argparse.ArgumentParser();p.add_argument('--factor',type=int,default=2)
    p.add_argument('--length',type=int,default=2048);p.add_argument('--beam',type=int,default=2048)
    p.add_argument('--seconds',type=float,default=210);p.add_argument('--full-image',type=int,default=0)
    a=p.parse_args();start=time.monotonic();checked=controls();states=[(0,0,0,0,0,0,0)];records=[]
    banned=[(6,26)]
    if a.full_image:
        r=json.loads((HERE/f'right-free-language-{a.full_image}.json').read_text(encoding='utf-8'))
        allowed=set(words(a.full_image,True))-{int(s[::-1],2) for s in r['missing_words_lsb_time_first']}
        banned=[]
        for k in range(1,a.full_image+1):
            missing=set(words(k,True))-{w&((1<<k)-1) for w in allowed}
            for v in sorted(missing):
                if any(any((v>>j)&((1<<h)-1)==q for j in range(k-h+1)) for h,q in banned):continue
                banned.append((k,v))
    for d in range(a.length):
        choices=[];mask=(1<<(2*d+2))-1
        for R,Rm,u,w,z,run,cost in states:
            R1,old=step(R,Rm,2*d,1);base,_=step(R1,old,2*d+1,0);pred=(base>>(2*d+1))&1
            for s in [0,1]:
                if (not s and d and run==0) or (s and run==4):continue
                nw=w|(s<<d)
                if any(d+1>=k and (nw>>(d+1-k))&((1<<k)-1)==v for k,v in banned):continue
                e=pred^s
                choices.append((base^(mask if s else 0),R1,u|(e<<d),nw,z+1-s,run+1 if s else 0,cost+e))
        assert choices
        choices.sort(key=lambda q:(a.factor*q[6]-q[4],q[6],q[2]));states=choices[:a.beam];best=states[0]
        deficit=a.factor*best[6]-best[4]
        if deficit<0 or (d+1)%64==0 or d+1==a.length:
            rec={'length':d+1,'deficit':deficit,'even_black_count':best[6],'free_zeros':best[4],
                 'seconds':round(time.monotonic()-start,3)};records.append(rec);print(rec,flush=True)
        if deficit<0:reason='counterexample_found';break
        if time.monotonic()-start>a.seconds:reason='self_time_limit';break
    else:reason='length_completed'
    free=check_full(best[3],best[2],d+1)
    assert all(not any(free[j:j+k]==[(v>>i)&1 for i in range(k)] for j in range(len(free)-k+1)) for k,v in banned)
    out={'factor':a.factor,'beam':a.beam,'length':d+1,'six_word_constraint_kernel_verified':True,
         'additional_image_constraints_numerical_only':a.full_image,'counterexample_found':deficit<0,
         'forbidden_patterns':[{'length':k,'lsb_time_first':''.join(str(v>>i&1) for i in range(k))} for k,v in banned],
         'final_deficit':deficit,'even_black_count':best[6],'free_zeros':best[4],
         'free_prefix':free,'even_input_hex':hex(best[2]),'free_prefix_hex':hex(best[3]),
         'independent_scalar_and_physical_reencoding_passed':True,'controls':checked,'records':records,
         'stop_reason':reason,'Lean_verified':False,'unbounded_charge_proved':False,'full_problem_solved':False,
         'seconds':round(time.monotonic()-start,3)}
    save(f'charge-coupled-factor{a.factor}-image{a.full_image}.json',out)
    print({k:v for k,v in out.items() if k not in ('free_prefix','records','controls')},flush=True)

if __name__=='__main__':main()
