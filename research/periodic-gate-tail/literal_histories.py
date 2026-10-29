from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parent;words=json.loads((ROOT/'WORDS.json').read_text())
def R(p,k):return (words[(k+153)%155]>>(p%10))&1
def inverse(row,b):
    out=[0,b]
    for k in range(1,len(row)-1):
        choices=[z for z in [0,1] if ((30>>(4*z+2*out[k]+out[k-1]))&1)==row[k]]
        assert len(choices)==1;out.append(choices[0])
    return out
D=1+620*5+155;base=[0]+[R(0,k) for k in range(1,D)]
# Check the base's physical zero-wall boundary by direct rule-table forward evolution.
temp=base[:];boundary=[]
for t in range(20):
    boundary.append(temp[1]);assert temp[1]==int(t%10!=0)
    temp=[0]+[(30>>(4*temp[k+1]+2*temp[k]+temp[k-1]))&1 for k in range(1,len(temp)-1)]
records=[]
for gates,maxn,step in [(False,6,310),(True,5,620)]:
    level={0:base}
    for n in range(maxn+1):
        for code,row in level.items():
            phase=(18 if gates else 9)*n
            bad=[k for k in range(1,len(row)) if row[k]!=R(phase,k)]
            assert not bad or max(bad)<1+step*n,(gates,n,code,max(bad))
            records.append({'gate_history':gates,'steps':n,'code':code,'largest_difference_from_reference':max(bad,default=None),'proved_bound':1+step*n,'checked_cells':len(row),'row_sha256':hashlib.sha256(bytes(row)).hexdigest()})
        if n==maxn:break
        nxt={}
        for code,row in level.items():
            for b in [0,1]:
                nxt[code+(b<<n)]=inverse(inverse(row,1),1-b) if gates else inverse(row,b)
        level=nxt
S={8,9,16,18,33,36,66,72,132,144}
windows=[sum(int((r+i)%5==0)<<i for i in range(8)) for r in range(5)]
assert all(w in S for w in windows)
out={'passed':True,'literal_inverse_rows':len(records),'forward_boundary_ticks_checked':20,'gate_windows':windows,'all_gate_windows_in_S':True,'records':records,'kernel_verified':False}
(ROOT/'LITERAL-HISTORIES.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='records'}))
