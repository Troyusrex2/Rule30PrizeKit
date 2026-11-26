"""Replay the origin controls with the standard library, integer arithmetic only."""
import json
from itertools import product
from pathlib import Path

from descent import delta, macro
from mature import tested


def trace(east, clock):
    col = []
    for c in clock:
        col.append(east & 1)
        east = ((east << 1) | c) ^ (east | (east >> 1))
    return col


def check_tiles():
    # Consecutive B tiles contain these nine row masks; the carrier is the easternmost bit.
    b = (24,12,22,18,31,0,0,0,16)
    rows = ((16,)+b+b)[4:13]
    assert rows == (18,31,0,0,0,16,24,12,22)
    clock = [x >> 4 for x in rows]
    for start in range(256):
        east = trace(start, clock[:-1])
        assert any((y >> 4) != (((x >> 3) & 1) ^ ((x >> 4) | v))
                   for x,y,v in zip(rows,rows[1:],east))
    print("BB forbidden: all 256 physical eastern prefixes fail.")


def check_protection():
    count = 0
    for bits in product(range(2), repeat=3):
        seq = [b ^ (k%2) for b in bits for k in range(4)]
        for off in range(4):
            clock = seq[off:off+9]
            for seed in range(256):
                # Only eight east samples enter four inversions for five outputs.
                c, r = clock, trace(seed, clock[:-1])
                for _ in range(4):
                    c, r = [n ^ (b | z) for n,b,z in zip(c[1:],c,r)], c
                assert len(c) == 5 and c != [1,0,1,0,1]
                count += 1
    print("Alternating four-bit blocks: all",count,"local cases pass.")


def check_descent():
    cert = json.loads(Path(__file__).with_name('descent-k5.json').read_text())
    assert all(weight > 0 and macro(x) is not None for x,weight in cert)
    changes = [delta(x,5) for x,_ in cert]
    assert all(sum(weight*d for (_,weight),d in zip(cert,col))==0 for col in zip(*changes))
    print("Width-five strict descent veto: 63 exact zero sums on",len(cert),"finite western rows.")
    mature = json.loads(Path(__file__).with_name('mature-k5.json').read_text())
    assert all(m>0 for _,_,m in mature)
    cols = zip(*(delta(tested(slot,tail),5) for slot,tail,_ in mature))
    assert all(sum(m*d for (*_,m),d in zip(mature,col))==0 for col in cols)
    print("Same veto within true 27-tick 011 windows on",len(mature),"finite full rows.")


def check_ether():
    rows = [3984,249,2319]
    for x,y in zip(rows, rows[1:]+rows[:1]):
        assert (((x<<1|x>>11) ^ (x|x>>1|x<<11)) & 4095)==y
    def deficit_at(j):
        a=[(x>>(j%12))&1 for x in rows]
        b=[(x>>((j+1)%12))&1 for x in rows]
        return 3-3*sum(a)+6*sum(q*(1-r) for q,r in zip(a,b))
    assert [deficit_at(j) for j in (-2,-1)]==[0,3]
    print("12-site periodic control: three-tick deficits 0 and 3.")


if __name__ == '__main__':
    check_tiles()
    check_protection()
    check_descent()
    check_ether()
