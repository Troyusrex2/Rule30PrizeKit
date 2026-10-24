"""Exact shared instruments for the seven-agent campaign; not proof premises."""
from pathlib import Path
import importlib.util
import json
import random
import sys

HERE=Path(__file__).resolve().parent
REPO=next((p for p in HERE.parents if (p/'research/normalization-first-meeting/replay.py').is_file()),
          HERE.parents[1]/'overnight-20261024')
BASE=REPO.parent


def phi(a): return a ^ ((a<<1)|(a<<2))


def rows(a,n):
    for _ in range(n):
        yield a
        a=phi(a)


def trace(a,c,n):
    word=0
    for t in range(n):
        word|=((a>>(c+t))&1)<<t
        a=phi(a)
    return word


def seedlow(a): return bool(a&1) and ((a>>1)&1)==((a>>2)&1)


def canonical(T,P):
    x=1
    for _ in range(T):x=phi(x)
    y=x
    for _ in range(P):y=phi(y)
    return x<<P,y,T+P


def controls():
    rng=random.Random(30701);count=0
    for _ in range(48):
        a=rng.randrange(1,1<<10);c=rng.randrange(10)
        physical={c-i:(a>>i)&1 for i in range(a.bit_length())}
        for t in range(13):
            for i in range(a.bit_length()+2):
                assert ((a>>i)&1)==physical.get(c+t-i,0)
                count+=1
            lo,hi=min(physical),max(physical)
            old=physical
            physical={p:(30>>((old.get(p-1,0)<<2)|(old.get(p,0)<<1)|old.get(p+1,0)))&1
                      for p in range(lo-1,hi+2)}
            a=phi(a)
    # Same physical configuration in two integer frames: a trace-only class
    # reader cannot infer bit0 without the center index (or a fixed frame).
    for t in range(128):
        assert trace(2,1,t+1)==trace(1,0,t+1)
    return {'all_passed':True,'physical_truth_table_cell_comparisons':count,
            'translated_trace_controls':128}


def guarded_script(script,log,args=()):
    spec=importlib.util.spec_from_file_location('resource_guard',
        REPO/'research/normalization-first-meeting/replay.py')
    g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
    return g.guarded([sys.executable,str(script),*map(str,args)],HERE,log)


def save(name,value):
    (HERE/name).write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8',newline='\n')
