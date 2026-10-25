"""Independent stress tests of the eventually-alternating Theta conjecture."""
import importlib.util,json,random,time
from pathlib import Path
root=Path(__file__).resolve().parent
src=root/'snapshots/r30-coinailyzer-wiki-20261025T124335Z-f16dc412-v01/src/coupled_core.py'
spec=importlib.util.spec_from_file_location('wiki_coupled_core',src)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
started=time.monotonic();rng=random.Random(30261025);failures=[];checked=0
def golden(prefix):return all(prefix[i:i+2]!=[0,0] for i in range(len(prefix)-1)) and all(prefix[i:i+5]!=[1]*5 for i in range(len(prefix)-4))
for length in [20,32,48,64,96,128]:
    for sample in range(100):
        prefix=[0];ones=0
        while len(prefix)<length:
            bit=1 if prefix[-1]==0 else (0 if ones>=4 else rng.randrange(2))
            prefix.append(bit);ones=ones+1 if bit else 0
        # Start an alternating tail with a legal join, forever from this point.
        tailfirst=1-prefix[-1]
        f=prefix+[(tailfirst^(j%2)) for j in range(4098)]
        assert golden(f)
        psi=m.psi_row(f,8192)
        tail=psi[4096:8193]
        bad=next((i for i in range(len(tail)-28) if tail[i]!=tail[i+28]),None)
        density=sum(tail)/len(tail)
        checked+=1
        if bad is not None or density<2/7-0.005:
            failures.append({'prefix_length':length,'sample':sample,'prefix_bits':''.join(map(str,prefix)),
                             'period28_failure_at_depth':None if bad is None else 4096+bad,
                             'finite_tail_black':sum(tail),'finite_tail_length':len(tail),'finite_density':density})
            if len(failures)>=12:break
    if len(failures)>=12:break
# Reproduce the two explicit witnesses, preserving finite/infinite distinction.
witnesses=[]
for code in [0xd6e0,0x888,0x72270]:
    z,b,f,psi=m.counts(code,20000)
    witnesses.append({'position_p_at_bit_p_hex':hex(code),'n':20000,'zeros':z,'black_count':b,
                      'C2_excess':5*z-20000-2*b,'C3_excess':5*z-20000-3*b,
                      'free_prefix':''.join(map(str,f[:40]))})
out={'finite_only':True,'Lean_verified':False,'rng_seed':30261025,'eventually_alternating_samples':checked,
     'late_window_counterexamples_or_stress_cases':failures,'actual_finite_right_witnesses':witnesses,
     'logical_gap':'Maximal limiting zero density does not imply eventual alternation: insert an extra one in block 01 at powers-of-two block indices. The stream remains Golden, has zero density1/2, and infinitely many11 slips. Also bounds for eventually alternating streams do not cover all finite-R drivers.',
     'seconds':time.monotonic()-started}
(root/'wiki-followup.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
