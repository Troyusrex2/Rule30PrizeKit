from pathlib import Path
import json,time
from cohomology_probe import image
ROOT=Path(__file__).resolve().parent

def anf(table):
    a=table.copy();n=(len(a)-1).bit_length()
    for j in range(n):
        for s in range(len(a)):
            if (s>>j)&1:a[s]^=a[s^(1<<j)]
    return a

def quotient(poly):
    out=set()
    for s,v in enumerate(poly):
        if not v:continue
        shape=s//(s&-s) if s else 0
        if shape in out:out.remove(shape)
        else:out.add(shape)
    return out

def main():
    start=time.monotonic();counts=[];bad=[]
    for w in range(1,5):
        cnt=0
        for density in range(1,1<<(1<<(w-1))):
            if time.monotonic()-start>30:raise TimeoutError('fixed cap')
            table=[((density>>(x>>1))&1) if x&1 else 0 for x in range(1<<w)]
            before=quotient(anf(table));m=max(s.bit_length() for s in before)
            after=quotient(anf([table[image(x,w)] for x in range(1<<(w+2))]))
            observed=max(s.bit_length() for s in after)
            expected=m+2 if m>=2 else 2
            cnt+=1
            if observed!=expected:bad.append({'width':w,'density':density,'span_before':m,'span_after':observed,'expected':expected})
        counts.append({'nominal_width':w,'nonzero_densities_checked':cnt})
    result={'status':'counterexample' if bad else 'not_refuted_in_fixed_range','counts':counts,
      'counterexamples':bad,'seconds':time.monotonic()-start,
      'scope':'Exact finite ANF computation; the uniform theorem is paper, not Lean.'}
    (ROOT/'span-result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
