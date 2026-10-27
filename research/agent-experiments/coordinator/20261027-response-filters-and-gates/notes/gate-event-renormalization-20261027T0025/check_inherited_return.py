"""One prescribed inherited orbit; no state, gap, or return search."""
import json
from pathlib import Path

def bit(n,t):
    return (n >> (t % 8)) & 1

profiles = [234,21,154,149,86,89,101,149]
def low_row(t):
    return sum(bit(v,t) << j for j,v in enumerate(profiles[:4]))
def tail4(t):
    return sum(bit(v,t) << j for j,v in enumerate(profiles[4:]))

def sigma(r,m):
    h,g,f,e = [(r >> j) & 1 for j in range(4)]
    a,b,c,d = [(m >> j) & 1 for j in range(4)]
    out = [h ^ ((e | a) & (1 ^ g ^ f)),
           g ^ ((a | b) & (1 ^ f ^ e)),
           f ^ ((b | c) & (1 ^ e ^ a)),
           e ^ ((c | d) & (1 ^ a ^ b))]
    return sum(v << j for j,v in enumerate(out))

times = [6,0,2,4]
rows = [low_row(t) for t in times] + [low_row(6)]
tails = [tail4(t) for t in times]
assert rows == [1,10,10,14,1]
assert tails == [7,14,13,11]
assert all(sigma(rows[j],tails[j]) == rows[j+1] for j in range(4))
assert all(bit(v,6) == 0 for v in profiles[1:4])
assert bit(profiles[4],6) == 1
out = {
    'status': 'PASS; one inherited infinite-tail control only',
    'prior_source': '../predecessor-periodicity-paper-20261026T2305/PAPER.md',
    'phases_mod8': times,
    'register_path': rows,
    'actual_tail_low_four_bits': tails,
    'return_time_D_steps': 8,
    'black_event_gap_at_both_ends': 4,
    'finite_support': False,
    'new_orbit_discovery': False,
    'new_lean_claim': False,
}
Path(__file__).with_name('CONTROL.json').write_text(
    json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
