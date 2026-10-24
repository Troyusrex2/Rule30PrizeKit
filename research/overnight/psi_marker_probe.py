"""Look for falsifiable dyadic black markers in the specific empty-right row.

Training and holdout depths are separated. No finite run establishes any
unbounded identity. Any survivor needs a mathematical argument and Lean proof.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import time

HERE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('sideways',HERE.parent/'global-periodicity/sideways-candidate.py')
sideways=importlib.util.module_from_spec(sp);sp.loader.exec_module(sideways)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--train',type=int,default=65536)
    ap.add_argument('--holdout',type=int,default=1048576)
    args=ap.parse_args();began=time.monotonic()
    train=sideways.candidate(0,args.train)
    candidates=[]
    for a in range(1,32,2):
        for b in range(-32,33):
            indices=[a*(1<<n)+b for n in range(24) if 1<=a*(1<<n)+b<=args.train]
            if len(indices)>=10 and all((train>>(m-1))&1 for m in indices):
                candidates.append({'a':a,'b':b,'training_observations':len(indices)})
    print(json.dumps({'training_depth':args.train,'candidate_count':len(candidates)}),flush=True)
    full=sideways.candidate(0,args.holdout)
    assert full&((1<<args.train)-1)==train
    for n in [1,2,3,8,31,64,127]:
        prefix=full&((1<<n)-1)
        assert sideways.direct_trace(prefix,0,n+1)==[1-t%2 for t in range(n+1)]
    for c in candidates:
        points=[(n,c['a']*(1<<n)+c['b']) for n in range(24)
                if args.train<c['a']*(1<<n)+c['b']<=args.holdout]
        c['holdout']=[{'n':n,'depth':m,'black':bool((full>>(m-1))&1)} for n,m in points]
        c['survives_finite_holdout']=all(p['black'] for p in c['holdout'])
    report={'finite_experiments_only':True,'unbounded_identity_proved':False,
            'row':'Rule30PeriodTwoSideways.Psi empty','training_depth':args.train,
            'holdout_depth':args.holdout,'candidate_form':'a*2^n+b, odd 1<=a<=31, -32<=b<=32',
            'candidates':candidates,'seconds':round(time.monotonic()-began,3),
            'row_integer_bytes_sha256':hashlib.sha256(full.to_bytes((args.holdout+7)//8,'little')).hexdigest()}
    (HERE/'psi-marker-probe.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__':main()
