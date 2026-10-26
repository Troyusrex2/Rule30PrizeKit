"""Independent literal paired-strip reconstruction; no clock or width census."""
from pathlib import Path
from itertools import product
from collections import deque
import hashlib,json,re
ROOT=Path(__file__).resolve().parent
PUBLISHED=ROOT/'published/work'
source=PUBLISHED/'Rule30PeriodicOrPairCertificate.lean'
reference=json.loads((PUBLISHED/'periodic-or-certificate.json').read_bytes())
RULE={(0,0,0):0,(0,0,1):1,(0,1,0):1,(0,1,1):1,(1,0,0):1,(1,0,1):0,(1,1,0):0,(1,1,1):0}
def encode(row):return sum(v<<j for j,v in enumerate(row))
def code(pair):return encode(pair[0])+64*encode(pair[1])
def rowstep(row,older):return tuple(older)+tuple(RULE[(row[j],row[j-1],row[j-2])] for j in range(2,6))
def advances(pair):
    return {(rowstep(pair[0],bits[:2]),rowstep(pair[1],bits[2:])) for bits in product((0,1),repeat=4)}
def good(pair):
    a,b=pair
    return (a[4] or a[5])==(b[4] or b[5]) and a[3]!=b[3] and a[2]==b[2]
rows=list(product((0,1),repeat=6))
levels=[{(a,b) for a in rows for b in rows if good((a,b))}]
for _ in range(3):levels.append({pair for pair in levels[-1] if advances(pair)&levels[-1]})
assert [len(level) for level in levels]==reference['level_counts']==[640,192,112,90]
lean=source.read_text(encoding='utf-8')
for i,level in enumerate(levels):
    values=json.loads(re.search(r'def level'+str(i)+r' : List Nat := (\[[^\n]+\])',lean).group(1))
    assert values==sorted(map(code,level))
live=levels[-1];successors={pair:advances(pair)&live for pair in live}
assert all(successors.values())
assert {str(code(pair)):sorted(map(code,following)) for pair,following in successors.items()}==reference['successors']
def projection(pair):return (pair[0][2:],pair[1][2:])
def pcode(p):return encode(p[0])+16*encode(p[1])
projections={projection(pair) for pair in live};reach={}
for p in projections:
    found={pair for pair in live if projection(pair)==p};todo=deque(found)
    while todo:
        current=todo.popleft()
        for middle in successors[current]:
            for nxt in successors[middle]:
                if nxt not in found:found.add(nxt);todo.append(nxt)
    assert all(projection(pair)!=(p[1],p[0]) for pair in found)
    reach[str(pcode(p))]=sorted(map(code,found))
assert len(projections)==reference['projection_count']==20
assert sum(map(len,reach.values()))==reference['projected_even_reach_pairs']==438
assert reach==reference['projection_even_reach']
# One literal finite-white odd-half-clock control; not a census.
def finite_update(row):
    padded=(0,0)+row
    return tuple(RULE[(padded[j+2],padded[j+1],padded[j])] for j in range(len(row)))
start=tuple((20>>j)&1 for j in range(7));orbit=[start];nxt=finite_update(start)
while nxt!=start:
    assert nxt not in orbit and len(orbit)<128
    orbit.append(nxt);nxt=finite_update(nxt)
period=len(orbit)
assert all(orbit[(t+1)%period][3]==1-orbit[t][3] and orbit[(t+1)%period][2]==orbit[t][2] for t in range(period))
or_periodic=all((orbit[(t+1)%period][5] or orbit[(t+1)%period][4])==(orbit[t][5] or orbit[t][4]) for t in range(period))
column_periodic=all(orbit[(t+1)%period][6]==orbit[t][6] for t in range(period))
assert or_periodic
out=dict(passed=True,level_counts=[len(level) for level in levels],projection_count=len(projections),
    projected_even_reach_pairs=sum(map(len,reach.values())),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    certificate_sha256=hashlib.sha256((PUBLISHED/'periodic-or-certificate.json').read_bytes()).hexdigest(),
    induction_scope='The exact two-step closure applies to every natural number of step pairs. Each actual infinite path lies in all three viability prunings. The two oldest inputs of each copy are independently free on every edge; no older period or clock truncation enters.',
    odd_control=dict(width=7,seed=20,older_first=list(start),j=0,R=1,full_orbit=[list(row) for row in orbit],
        orbit_period=period,source_antiperiod=True,older_period=True,newest_or_period=True,next_column_period=column_periodic),
    preserved_audit_failure='Attempt1 mistakenly required the odd-R OR counterexample also to make the next column R-periodic. The publication claimed only the OR counterexample. Its next column actually flips. The overstrong audit assertion/source/log are preserved.',
    kernel_scope='This independent script is an exact-computation audit. Separate unchanged-checker reports establish the Lean constants.')
(ROOT/'graph-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='odd_control'},indent=2))
