"""Extend left-edge measurements with a bounded ring instead of all-row storage."""
import json,time
from collections import deque
from pathlib import Path

start=time.monotonic()
periods=[2,4,6,8,10,12,14,16,24,32,48,56,64,80,96,128]
targets={1000,2000,4000,6000,7999,8192,16384,32768,65536,131072}
ring=deque(maxlen=129);row=1;records=[];constant_failures=[]
for t in range(131073):
    ring.append(row)
    if t in targets:
        depths={str(p):2*t+1-(row^(ring[-1-p]<<(2*p))).bit_length() for p in periods}
        for p in periods:
            valuation=(p&-p).bit_length()-1
            expected={1:8,2:29,3:400}.get(valuation)
            if expected is not None and depths[str(p)]!=expected:
                constant_failures.append({'t':t,'p':p,'depth':depths[str(p)],'expected':expected})
        records.append({'t':t,'width':2*t+1,'depths':depths,'p16_fraction':depths['16']/(2*t+1)})
    row=row^((row<<1)|(row<<2))
out={'finite_only':True,'last_time':131072,'stored_rows_maximum':129,'records':records,
     'low_valuation_constant_failures':constant_failures,'seconds':time.monotonic()-start,
     'note':'Alignment is the moving physical left edge. No semantic identification with the white-wall 26-cell barrier is made.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
