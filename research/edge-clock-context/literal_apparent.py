"""Independent rule-table check of the finite observation construction."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
out=[]
for n in list(range(65))+[128,256]:
    width=4*n+5
    initial=sum(7<<(4*i) for i in range(n))+(5<<(4*n))
    row=[(initial>>j)&1 for j in range(width)]
    first=None;trace=[]
    for t in range(8*n+33):
        actual=[row[4*n+3],row[4*n+4]]
        target=[(234>>(t%8))&1,(170>>(t%8))&1]
        if actual!=target:
            first=t;break
        trace.append(actual)
        row=[(30>>(4*row[j]+2*(row[j-1] if j>=1 else 0)+(row[j-2] if j>=2 else 0)))&1 for j in range(width)]
    assert first is None or first>2*n+1,(n,first)
    assert initial&1 and initial.bit_length()==4*n+3
    out.append({'n':n,'initial_word':str(initial),'initial_bit_length':initial.bit_length(),'observed_depths':[4*n+3,4*n+4],'guaranteed_through_tick':2*n+1,'first_pair_deviation':first,'searched_through':8*n+32,'prefix_matches_guarantee':True})
(ROOT/'LITERAL-APPARENT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'cases':len(out),'all_passed':True,'selected':[r for r in out if r['n'] in [0,1,2,4,8,16,32,64,128,256]]}))
