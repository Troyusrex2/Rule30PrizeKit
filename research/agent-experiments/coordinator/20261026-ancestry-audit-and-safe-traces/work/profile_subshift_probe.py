"""Test a precise unary rigidity target before attempting a proof."""
from pathlib import Path
import json,time
from mode_data import states_graph,rotate
r=Path(__file__).resolve().parent;start=time.monotonic();reports=[]
for P in [2,4,8,16,32,64]:
    states,word=states_graph(P);mask=(1<<P)-1;profiles={};counts={'no00':0,'no11':0,'no00_nonperiod2':0,'odd_black_nonperiod2':0};examples={}
    odds=sum(1<<t for t in range(1,P,2))
    for i,(h,g,d) in enumerate(states):profiles.setdefault(g,i)
    for g,i in profiles.items():
        no00=((mask^g)&rotate(mask^g,1,P))==0
        no11=(g&rotate(g,1,P))==0
        period2=rotate(g,2,P)==g
        counts['no00']+=no00;counts['no11']+=no11
        for kind,yes in [('no00_nonperiod2',no00 and not period2),('odd_black_nonperiod2',(g&odds)==odds and not period2)]:
            counts[kind]+=yes
            if yes and kind not in examples:examples[kind]={'initial':word(i),'profile':g}
    report={'clock':P,'unique_profiles':len(profiles),'counts':counts,'first_examples':examples};reports.append(report)
    print(json.dumps(report),flush=True)
out={'reports':reports,'all_ancestors_P_periodic':True,'Lean_verified':False,
     'uniform_unary_rigidity_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
(r/'profile-subshift-probe.json').write_text(json.dumps(out,indent=2)+'\n')
