"""Exact finite image of driven-right boundary words, using all input lanes.

This is finite computation, not a Lean theorem. Every right continuation has
the same output prefix as one enumerated finite input by the local light cone.
"""
import argparse,random,time
from core import save
from even_support_checker import pat
from empty_right_absorption import step
from even_code_charge import words

def main():
    p=argparse.ArgumentParser();p.add_argument('--length',type=int,default=12);a=p.parse_args()
    n=a.length;start=time.monotonic();N=1<<(2*n);ALL=(1<<N)-1
    row=[pat(2*n,j) for j in range(2*n)];free=[]
    for t in range(2*n-1):
        driver=ALL if t%2==0 else 0
        row=[(driver if j==0 else row[j-1])^(row[j]|row[j+1]) for j in range(len(row)-1)]
        if t%2==0:free.append(ALL^row[0])
    rng=random.Random(302490);cases=[0,N-1]+[rng.randrange(N) for _ in range(62)]
    for u in cases:
        x=u;f=[]
        for t in range(2*n-1):
            x=step(x,t)
            if t%2==0:f.append(1^(x&1))
        assert f==[(col>>u)&1 for col in free]
    image={};bad=0
    def visit(d,w,lanes,run):
        nonlocal bad
        if not lanes:return
        if d==n:
            image[w]=(lanes&-lanes).bit_length()-1;return
        for bit in [0,1]:
            q=lanes&(free[d] if bit else ALL^free[d])
            if not q:continue
            if (bit==0 and run==0) or (bit==1 and run==4):bad+=q.bit_count();continue
            visit(d+1,w|(bit<<d),q,(1 if run==5 else run+1) if bit else 0)
    visit(0,0,ALL,5);assert bad==0
    golden=set(words(n,True));assert set(image)<=golden
    missing=sorted(golden-set(image))
    out={'free_length':n,'initial_right_bits':2*n,'exhaustive_lanes':N,'image_words':len(image),
        'golden_words':len(golden),'additional_forbidden_words':len(missing),
        'missing_words_lsb_time_first':[''.join(str(w>>i&1) for i in range(n)) for w in missing],
        'first_image_witnesses':{str(w):u for w,u in list(sorted(image.items()))[:16]},
        'scalar_right_controls':len(cases),'all_controls_passed':True,'bad_golden_lanes':bad,
        'Lean_verified':False,'uniform_language_characterized':False,'full_problem_solved':False,
        'seconds':round(time.monotonic()-start,3)}
    save(f'right-free-language-{n}.json',out)
    print({k:v for k,v in out.items() if k not in ('missing_words_lsb_time_first','first_image_witnesses')},flush=True)

if __name__=='__main__':main()
