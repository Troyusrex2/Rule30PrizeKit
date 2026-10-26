"""Test specific adjacent-equality and period-drop hypotheses on prefix graphs."""
from pathlib import Path
import json,time
from mode_data import states_graph,rotate

r=Path(__file__).resolve().parent;start=time.monotonic();reports=[]
def period(x,P):
    p=P
    while p>1 and rotate(x,p//2,P)==x:p//=2
    return p
def literal(word,P):
    field=word.copy();initial=field.copy();older=[];newer=[]
    for t in range(P):
        older.append(field[-2] if len(field)>1 else 0)
        newer.append(field[-1] if field else 0)
        field=[(30>>(4*x+2*(field[i-1] if i else 0)+(field[i-2] if i>1 else 0)))&1
               for i,x in enumerate(field)]
    assert field==initial
    return sum(b<<t for t,b in enumerate(older)),sum(b<<t for t,b in enumerate(newer))
for P in [2,4,8,16,32,64]:
    states,word=states_graph(P);mask=(1<<P)-1
    equal_nonzero=equal_not_two=inclusions=drops=or_drops=0
    examples={}
    for i,(l,k,d) in enumerate(states):
        lp=period(l,P);kp=period(k,P);rp=period(l|k,P)
        tests={'equal_nonzero':l==k and k!=0,
               'equal_not_two':l==k and kp>2,
               'inclusion':(l&~k)==0,
               'period_drop':kp<lp,
               'OR_period_drop':rp<max(lp,kp)}
        equal_nonzero+=tests['equal_nonzero'];equal_not_two+=tests['equal_not_two']
        inclusions+=tests['inclusion'];drops+=tests['period_drop'];or_drops+=tests['OR_period_drop']
        if tests['inclusion']:assert l==k or (l==0 and k==mask)
        for kind in ['equal_not_two','period_drop','OR_period_drop']:
            if tests[kind] and kind not in examples:
                w=word(i);assert literal(w,P)==(l,k)
                examples[kind]={'initial':w,'older':l,'newer':k,'periods':[lp,kp,rp]}
    out={'clock':P,'states':len(states),'equal_nonzero_states':equal_nonzero,
         'equal_non_period_two_states':equal_not_two,'inclusion_states':inclusions,
         'period_drop_states':drops,'OR_period_drop_states':or_drops,'examples':examples}
    reports.append(out);print(json.dumps(out),flush=True)
out={'reports':reports,'all_prefix_ancestors_P_periodic':True,'finite_clocks_only':True,
     'Lean_verified':False,'uniform_no_period_drop_proved':False,
     'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
(r/'plateau-chain-probe.json').write_text(json.dumps(out,indent=2)+'\n')
