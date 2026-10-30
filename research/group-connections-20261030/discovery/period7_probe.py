from pathlib import Path
import time,json
ROOT=Path(__file__).resolve().parent
r=0;a=[];start=time.monotonic();bad=None
for t in range(65537):
    if time.monotonic()-start>30:raise TimeoutError('fixed period7 cap')
    if t%2==0:
        a.append(r&1);n=t//2
        if n>=9 and a[n]!=a[n-7]:
            bad={'earlier_sample':n-7,'later_sample':n,'earlier_time':2*(n-7),'later_time':t,
                 'earlier_bit':a[n-7],'later_bit':a[n]}
            break
    r=(r<<1)^(r|(r>>1))^(t&1)
result={'status':'refuted' if bad else 'not_refuted_in_fixed_range','first_counterexample':bad,
 'samples_checked':len(a),'sample_prefix':a[:512],'seconds':time.monotonic()-start}
(ROOT/'period7-result.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items() if k!='sample_prefix'})
