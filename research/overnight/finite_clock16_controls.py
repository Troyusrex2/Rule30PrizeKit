"""Independent finite controls accompanying the arbitrary-width Lean certificate."""
from collections import deque
import json
from pathlib import Path
import random
import re

from generate_finite_clock16 import pool


def q(a):return a^((a>>1)|(a>>2))


def orbit16(a):
    values=[a]
    for _ in range(16):values.append(q(values[-1]))
    return values


def profile(values,k):return sum(((a>>k)&1)<<t for t,a in enumerate(values[:16]))


def has_period(bits,H):
    return all((bits>>t)&1==(bits>>((t+H)%16))&1 for t in range(16))


def representatives():
    mask=65535;words={0:0};queue=deque([0])
    while queue:
        key=queue.popleft();b,c=key&mask,key>>16;bits=bit=0
        for t in range(16):bits|=bit<<t;bit^=((b|c)>>t)&1
        if bit:continue
        for value in (bits,bits^mask):
            target=value|(b<<16)
            if target not in words:words[target]=(words[key]<<1)|(value&1);queue.append(target)
    return words


def expand_tail(a):
    width=a.bit_length();assert width>=2
    n=width-2;top=a>>n;assert top in (2,3)
    return ((6 if top==2 else 5)<<n)|(a&((1<<n)-1))


def main():
    entries=pool(16);allowed={(b,c) for b,c,_,_ in entries}
    finite=pair_checks=detection_checks=0
    def check(a):
        nonlocal finite,pair_checks,detection_checks
        values=orbit16(a)
        if values[-1]!=a:return False
        finite+=1;columns=[profile(values,k) for k in range(a.bit_length()+2)]
        for k in range(len(columns)-1):assert (columns[k],columns[k+1]) in allowed;pair_checks+=1
        for H in range(16):
            if has_period(columns[0],H):assert values[H]==a;detection_checks+=1
        return True
    for a in range(1<<14):check(a)
    rng=random.Random(2026102411);reps=[w for w in representatives().values() if w.bit_length()>=2]
    samples=[]
    for _ in range(128):
        a=rng.choice(reps);width=rng.randrange(32,201)
        while a.bit_length()<width:a=expand_tail(a)
        assert check(a);samples.append(a)
    report={'finite_controls_only':True,'Lean_verified_by_this_program':False,'full_problem_claim':False,
            'all_small_words_checked':1<<14,'small_word_width':14,'full_clock16_words_checked':finite,
            'profile_pair_memberships_checked':pair_checks,'head_clock_residue_implications_checked':detection_checks,
            'wide_words_checked':len(samples),'wide_sample_max_width':max(a.bit_length() for a in samples),
            'AllPassed':True,'builtin_CA_control_sample_words':[str(a) for a in samples[:8]]}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    wl=Path(__file__).with_name('finite-clock16-check.wl')
    text=wl.read_text(encoding='utf-8')
    line='finiteClock16SampleWords = {'+','.join(report['builtin_CA_control_sample_words'])+'};'
    text,count=re.subn(r'finiteClock16SampleWords = \{[^}]*\};',lambda _:line,text)
    assert count==1
    wl.write_text(text,encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if 'sample_words' not in k}))


if __name__=='__main__':main()
