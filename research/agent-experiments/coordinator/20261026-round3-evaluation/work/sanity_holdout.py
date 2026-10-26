"""Held-out surgery cases; finite annulus tests do not establish regeneration."""
from pathlib import Path
import ast,json,time
ROOT=Path(__file__).resolve().parent
path=ROOT/'snapshots/r30-codex-sanity-20261026T005702Z-9cfc0376-v01/src/experiment.py'
parsed=ast.parse(path.read_text())
functions=[node for node in parsed.body if isinstance(node,ast.FunctionDef) and node.name in ['g','forward','inverse_trace','physical','surgery','first_set']]
ns={};exec(compile(ast.Module(body=functions,type_ignores=[]),str(path),'exec'),ns)
forward,inverse,surgery=ns['forward'],ns['inverse_trace'],ns['surgery']
n=16384;c=forward(1,n);assert inverse(c,n)==1
cases=[];failures=[];least=None;start=time.monotonic()
for i in range(96):
    T=17+(i*71)%1000;P=17+(i*97)%1000
    u=surgery(c,T,P,n);b=inverse(u,n)
    assert forward(b,n)==u
    m=2*(T+P+1);annuli=[]
    while 2*m<=n:
        count=(b>>m&((1<<m)-1)).bit_count()
        annuli.append({'start':m,'end':2*m,'edits':count})
        if count==0:failures.append({'T':T,'P':P,'start':m})
        candidate={'T':T,'P':P,'start':m,'length':m,'edits':count}
        if least is None or count*least['length']<least['edits']*m:least=candidate
        m*=2
    cases.append({'T':T,'P':P,'annuli':annuli})
    assert time.monotonic()-start<240
report={'finite_only':True,'Lean_verified':False,'bits':n,'held_out_cases':len(cases),
        'complete_annuli':sum(len(c['annuli']) for c in cases),'fixed_M_failures':failures,
        'least_populated_fraction':least,'cases':cases,'regeneration_proved':False,'full_problem_solved':False}
(ROOT/'sanity-holdout.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='cases'}),flush=True)
