"""Sparse LP discovery with exact rational checking of every returned certificate.
An unchecked numerical infeasibility result is not an exact impossibility proof.
"""
from pathlib import Path
from fractions import Fraction
from collections import defaultdict
import json,sys,time,math
root=Path(__file__).resolve().parent
base=root.parents[2]/'toolchain'
sys.path[:0]=[str(base/'highs-python'),str(base/'semidefinite-research')]
import numpy as np
import highspy
dfa=json.loads((root/'learned-reader.json').read_bytes())['dfa']
def changed(s,p,r):return (((s>>1)^((p>>1)|(r>>1)))<<1)|((s&1)^((p&1)|(r&1)))
def graph(K):
    base=4**K;initial=(0,0,0,0,0,0,0)
    states=[initial];ids={initial:0};edges=[];at=0
    while at<len(states):
        if len(states)>15000:raise RuntimeError('graph cap')
        a,b,p,r,ca,cb,np=states[at]
        for s in range(4):
            ns=changed(s,p,r)
            t=(dfa['transitions'][a][s],dfa['transitions'][b][ns],s,p,(ca*4+s)%base,(cb*4+ns)%base,ns)
            if t not in ids:ids[t]=len(states);states.append(t)
            edges.append((at,ids[t],(a,ca,s),(b,cb,ns)))
        at+=1
    targets={i for i,(a,b,p,r,ca,cb,np) in enumerate(states) if a==15 and p in (0,3) and np in (0,3)}
    rev=[[] for _ in states]
    for s,t,_,_ in edges:rev[t].append(s)
    relevant=set(targets);stack=list(targets)
    while stack:
        for s in rev[stack.pop()]:
            if s not in relevant:relevant.add(s);stack.append(s)
    return states,[e for e in edges if e[0] in relevant and e[1] in relevant],sorted(relevant),sorted(targets)
reports=[]
for K,moment in [(2,True),(3,False),(3,True),(4,False),(4,True)]:
    start=time.monotonic();states,edges,nodes,targets=graph(K)
    fs=sorted({f for _,_,a,b in edges for f in (a,b)});cols={};rows=[];rhs=[]
    def var(kind,key):
        name=(kind,key)
        if name not in cols:cols[name]=len(cols)
        return cols[name]
    def row(terms,b=0):
        d=defaultdict(int)
        for kind,key,c in terms:
            if kind in ('A','W') and not moment:continue
            d[var(kind,key)]+=c
        d={i:c for i,c in d.items() if c}
        if d or b:rows.append(d);rhs.append(b)
    row([('B',0,1)]);row([('B',0,-1)])
    for s,t,a,b in edges:
        row([('W',a,1),('W',b,-1),('A',s,1),('A',t,-1)])
        row([('V',a,1),('V',b,-1),('B',s,1),('A',t,-1),('B',t,-1)])
    for t in targets:row([('A',t,1)]);row([('B',t,1)],1)
    lp=highspy.HighsLp();lp.num_col_=len(cols);lp.num_row_=len(rows)
    lp.col_cost_=np.zeros(len(cols));lp.col_lower_=np.full(len(cols),-highspy.kHighsInf)
    lp.col_upper_=np.full(len(cols),highspy.kHighsInf)
    lp.row_lower_=np.array(rhs,dtype=float);lp.row_upper_=np.full(len(rows),highspy.kHighsInf)
    starts=[0];indices=[];values=[]
    for d in rows:
        for j,v in sorted(d.items()):indices.append(j);values.append(v)
        starts.append(len(indices))
    lp.a_matrix_.format_=highspy.MatrixFormat.kRowwise
    lp.a_matrix_.start_=np.array(starts,dtype=np.int32)
    lp.a_matrix_.index_=np.array(indices,dtype=np.int32);lp.a_matrix_.value_=np.array(values,dtype=float)
    solver=highspy.Highs();solver.setOptionValue('output_flag',False)
    solver.setOptionValue('time_limit',15.0);solver.setOptionValue('threads',1)
    solver.setOptionValue('presolve','off');solver.setOptionValue('solver','simplex')
    solver.passModel(lp);solver.run();status=solver.getModelStatus()
    rec={'context':K,'first_moment':moment,'states':len(states),'features':len(fs),'rows':len(rows),
         'variables':len(cols),'numerical_status':str(status),'exact_certificate':False}
    cert=None
    if status==highspy.HighsModelStatus.kInfeasible:
        _,exists,ray=solver.getDualRay()
        if exists:
            for sign in (1,-1):
                y=[Fraction(float(sign*v)).limit_denominator(1000000) for v in ray]
                if any(v<0 for v in y):continue
                sums=defaultdict(Fraction)
                for d,v in zip(rows,y):
                    if v:
                        for j,c in d.items():sums[j]+=v*c
                margin=sum((v*b for v,b in zip(y,rhs)),Fraction())
                if all(v==0 for v in sums.values()) and margin>0:
                    cert={'kind':'farkas','nonzero_weights':[[i,str(v)] for i,v in enumerate(y) if v],
                          'rhs_margin':str(margin),'rational_dot_products_all_zero':True}
                    break
    elif status==highspy.HighsModelStatus.kOptimal:
        x=[Fraction(float(v)).limit_denominator(1000000) for v in solver.getSolution().col_value]
        if all(sum((x[j]*v for j,v in d.items()),Fraction())>=b for d,b in zip(rows,rhs)):
            cert={'kind':'feasible','values':[str(v) for v in x]}
    if cert is not None:
        rec['exact_certificate']=True;rec['certificate_kind']=cert['kind']
        payload={'certificate':cert,'rows':[{str(j):v for j,v in d.items()} for d in rows],
                 'rhs':rhs,'column_names':[[kind,key] for kind,key in cols]}
        name=f'lp-certificate-{K}-{int(moment)}.json'
        (root/name).write_text(json.dumps(payload,indent=2)+'\n',encoding='utf-8');rec['certificate_file']=name
    rec['seconds']=round(time.monotonic()-start,3);reports.append(rec);print(json.dumps(rec),flush=True)
    (root/'graph-lp.json').write_text(json.dumps({'reports':reports,'Lean_verified':False,
        'sink_separation_proved':False,'full_problem_solved':False},indent=2)+'\n',encoding='utf-8')
    if cert is not None and cert['kind']=='feasible':break
