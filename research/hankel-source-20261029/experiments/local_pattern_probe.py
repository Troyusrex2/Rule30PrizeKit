from pathlib import Path
import json,time
ROOT=Path(__file__).resolve().parent
K=4100;r=1<<K;first=None;start=time.monotonic()
for t in range(4097):
    if time.monotonic()-start>10:raise TimeoutError('new fixed structural cap')
    word=[(r>>(K+p))&1 for p in range(-2,3)]
    if word==[1,0,1,0,0]:
        nextrow=(r<<1)^(r|(r>>1));next2=(nextrow<<1)^(nextrow|(nextrow>>1))
        first={'time':t,'spatial_word_at_minus2_through2':word,
          'center_triple':[(r>>K)&1,(nextrow>>K)&1,(next2>>K)&1],
          'source_right_neighbor':(nextrow>>(K+1))&1,
          'shifted_integer_H2_determinant':((r>>K)&1)*((next2>>K)&1)-((nextrow>>K)&1)**2}
        break
    r=(r<<1)^(r|(r>>1))
result={'status':'forbidden_pattern_candidate_refuted' if first else 'not_refuted_in_fixed_range',
 'first_counterexample':first,'seconds':time.monotonic()-start,
 'scope':'Leading-border-only integer candidate is unchanged; no retained row census.'}
(ROOT/'local-pattern-result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
