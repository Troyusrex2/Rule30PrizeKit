from pathlib import Path
import json,time
ROOT=Path(__file__).resolve().parent
r=0;cols=[];records=[];start=time.monotonic()
for t in range(257):
    if time.monotonic()-start>10:raise TimeoutError('fixed cap')
    if t<128:cols.append(r&1)
    if t>=2 and t&(t-1)==0:
        expected=1<<(t-2)
        records.append({'time':t,'matches_single_restart':r==expected,'black_cells':r.bit_count(),
                        'lowest_black_index':(r&-r).bit_length()-1 if r else None})
    r=(r<<1)^(r|(r>>1))^(t&1)
result={'candidate_status':'refuted' if any(not x['matches_single_restart'] for x in records) else 'not_refuted',
 'dyadic_records':records,'column1_prefix':cols,'white_phase_prefix':cols[::2],'seconds':time.monotonic()-start}
(ROOT/'right-drive-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['candidate_status'],records)
print('white_phase_prefix',''.join(map(str,cols[::2])))
