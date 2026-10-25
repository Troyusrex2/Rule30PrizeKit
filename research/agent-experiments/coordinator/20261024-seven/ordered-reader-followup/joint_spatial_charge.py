"""Falsify a charge against both odd and even reconstructed spatial bits.

Heuristic beam only: a surviving finite prefix does not prove a uniform bound.
Independent physical evolution checks the entire returned prefix.
"""
import argparse,random,time
from core import save
from charge_beam_packed import step,controls
from coupled_even_code_probe import packed_run

def physical(row,free):
    for d,s in enumerate(free):
        assert row&1==1
        row=packed_run(row,1)
        assert row&1==s
        row=packed_run(row,1)
    return 2*len(free)

def main():
    p=argparse.ArgumentParser();p.add_argument('--factor',type=int,default=1);p.add_argument('--beam',type=int,default=2048)
    p.add_argument('--length',type=int,default=4096);p.add_argument('--seconds',type=float,default=180);p.add_argument('--seven',action='store_true');a=p.parse_args()
    start=time.monotonic();checked=controls();rng=random.Random(302526);ncontrol=0
    for _ in range(12):
        R=Rm=spatial=0;f=[]
        for d in range(32):
            s=rng.randrange(2);r,old=step(R,Rm,2*d,1);spatial|=((r>>(2*d))&1)<<(2*d)
            R,Rm=step(r,old,2*d+1,s);spatial|=((R>>(2*d+1))&1)<<(2*d+1);f.append(s)
        ncontrol+=physical(spatial,f)
    # R,Rm,free word,spatial word,zeros,run,black spatial count.
    states=[(0,0,0,0,0,0,0)];records=[];stopped='length_completed'
    for d in range(a.length):
        children=[];mask=(1<<(2*d+2))-1
        for R,Rm,word,spatial,z,run,cost in states:
            r,old=step(R,Rm,2*d,1);odd=(r>>(2*d))&1;base,_=step(r,old,2*d+1,0);pred=(base>>(2*d+1))&1
            for s in (0,1):
                if (not s and d and not run) or (s and run==4):continue
                w=word|(s<<d)
                if a.seven:
                    if d>=5 and (w>>(d-5))&63==26:continue
                    if d>=6 and (w>>(d-6))&127==45:continue
                even=pred^s
                children.append((base^(mask if s else 0),r,w,spatial|(odd<<(2*d))|(even<<(2*d+1)),z+1-s,run+1 if s else 0,cost+odd+even))
        children.sort(key=lambda q:(a.factor*q[6]-q[4],q[6],q[3]));states=children[:a.beam];best=states[0];score=a.factor*best[6]-best[4]
        if (d+1)%64==0 or score<0:
            records.append({'length':d+1,'spatial_black_count':best[6],'free_zeros':best[4],'deficit':score,'seconds':round(time.monotonic()-start,3)})
            print(records[-1],flush=True)
        if score<0:stopped='counterexample';break
        if time.monotonic()-start>a.seconds:stopped='time_budget';break
    f=[best[2]>>i&1 for i in range(d+1)];assert all(f[j:j+2]!=[0,0] and f[j:j+5]!=[1]*5 for j in range(len(f)))
    if a.seven:assert all(f[j:j+6]!=[0,1,0,1,1,0] and f[j:j+7]!=[1,0,1,1,0,1,0] for j in range(len(f)))
    comparisons=physical(best[3],f);assert best[3].bit_count()==best[6] and f.count(0)==best[4]
    save('joint-spatial-charge'+('-seven' if a.seven else '')+f'-c{a.factor}.json',{'factor':a.factor,'beam':a.beam,'short_guard_seven':a.seven,'completed_length':len(f),
         'stop_reason':stopped,'records':records,'final_deficit':score,'final_free_zeros':best[4],'final_spatial_black_count':best[6],
         'spatial_prefix_hex':hex(best[3]),'free_prefix_hex':hex(best[2]),'controls':{**checked,'physical_cell_comparisons':ncontrol+comparisons,'all_passed':True},
         'heuristic_only':True,'Lean_verified':False,'uniform_bound_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)})
    print({'stop_reason':stopped,'length':len(f),'deficit':score,'physical_recheck':True},flush=True)
if __name__=='__main__':main()
