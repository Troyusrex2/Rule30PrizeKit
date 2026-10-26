"""Audit observation offsets and long-horizon periodic-run extrapolations."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
def trace(seed,n,c=0):
    row=seed;result=bytearray(n)
    for t in range(n):
        j=t+c
        result[t]=(row>>j)&1 if j>=0 else 0
        row^=(row<<1)|(row<<2)
    return result
def best(seq):
    result={'equalities':0}
    for p in range(1,17):
        run=0
        for i in range(len(seq)-p):
            run=run+1 if seq[i]==seq[i+p] else 0
            if run>result['equalities']:
                result={'equalities':run,'period':p,'start':i-run+1,'periodic_block_length':run+p}
    return result
records=[]
for width in range(1,5):
    for seed in range((1<<(width-1))|1,1<<width,2):
        seq=trace(seed,65536)
        old=best(seq[:8*width+64]);new=best(seq)
        records.append({'width':width,'seed':seed,'old_horizon':8*width+64,'old_record':old,'new_record':new})
        # Literal physical-coordinate control, keeping the original observer.
        row={-j for j in range(seed.bit_length()) if seed>>j&1}
        for t in range(96):
            assert int(0 in row)==seq[t]
            row={p for p in range(min(row)-1,max(row)+2)
                 if ((p-1 in row)^((p in row) or (p+1 in row)))}
offsets=[]
for c in [8,16,64]:
    seq=trace(1,c+2,c)
    assert not any(seq[:c]) and seq[c]==1
    offsets.append({'initial_support_width':1,'observation_depth':c,'initial_zero_run':c,'first_black':c})
report={'finite_only':True,'Lean_verified':False,'records':records,'offset_controls':offsets,
        'scope_correction':'A restarted seed row at age T needs observation bit u+T, not bit u. A bound for all translations cannot depend on support width alone.',
        'run_length_correction':'The submitted r is a count of equalities; its periodic block has length r+p.',
        'uniform_bound_for_normalized_rows_proved_or_disproved':False,'full_problem_solved':False}
(ROOT/'backend-holdout.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'records':len(records),'offset_controls':offsets,'full_problem_solved':False}),flush=True)
