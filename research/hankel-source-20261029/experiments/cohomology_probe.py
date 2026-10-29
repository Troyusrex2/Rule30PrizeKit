from pathlib import Path
import json,time

ROOT=Path(__file__).resolve().parent

def rank(rows):
    basis={}
    for v in rows:
        while v:
            p=v.bit_length()-1
            if p in basis:v^=basis[p]
            else:
                basis[p]=v
                break
    return len(basis)

def image(word,k):
    return sum(( ((word>>j)&1)^(((word>>(j+1))&1)|((word>>(j+2))&1)) )<<j for j in range(k))

def main():
    start=time.monotonic();records=[]
    for k in range(1,9):
        nr=1<<k;nj=2*nr;rm=nr-1;jm=nj-1
        rows=[];jrows=[];trivial=[]
        for w in range(1<<(k+2)):
            if time.monotonic()-start>30:raise TimeoutError('fixed preregistered cap')
            old=(w>>1)&rm;new=image(w,k)
            jl=w&jm;jr=(w>>1)&jm
            jv=(1<<jl)^(1<<jr)
            rows.append((1<<old)^(1<<new)^(jv<<nr))
            jrows.append(jv)
        full=rank(rows);jr=rank(jrows)
        projected=nr-full+jr
        assert jr==nj-1
        for h in range(1<<(k-1)):
            density=0
            for w in range(nr):
                if ((w&((1<<(k-1))-1))==h)^((w>>1)==h):density|=1<<w
            trivial.append(density)
        trivial.append((1<<nr)-1)
        tr=rank(trivial)
        assert tr==(1<<(k-1))
        assert projected>=tr
        records.append({'width':k,'density_unknowns':nr,'flux_unknowns':nj,'constraints':len(rows),
          'constraint_rank':full,'flux_rank':jr,'density_dimension':projected,
          'trivial_dimension':tr,'nontrivial_quotient_dimension':projected-tr})
    result={'status':'no_nontrivial_charge_in_fixed_range' if all(r['nontrivial_quotient_dimension']==0 for r in records) else 'nontrivial_charge_exists',
      'records':records,'seconds':time.monotonic()-start,'scope':'Exact finite GF2 rank; not a theorem beyond width 8; not a Lean proof.'}
    (ROOT/'cohomology-result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
