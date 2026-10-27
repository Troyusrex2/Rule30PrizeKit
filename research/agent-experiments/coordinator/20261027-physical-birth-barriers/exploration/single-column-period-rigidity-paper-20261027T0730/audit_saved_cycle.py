"""Validate one saved cycle, without traversing or searching any state graph."""
import hashlib, json
from pathlib import Path

phase = Path(__file__).resolve().parent
source = phase.parent / 'physical-ring-column-period-20261027T0730/INVERSE-RESULT.json'
saved = json.loads(source.read_text(encoding='utf-8'))
cand = saved['candidate']
cycle = cand['cycle']
assert cand['clock'] == 6 and len(cycle) == 84
assert len(set(cycle)) == 84
assert all(0 <= n < 4096 for n in cycle)
origin = cand['pair_index']

# The high six bits are the left column a, low six bits its right neighbor b.
# Saved traversal is toward the physical left, hence physical column j uses
# the first component at saved index origin-j. No shift in physical time.
def profile(j):
    return cycle[(origin-j) % 84] // 64
def cell(t, j):
    return (profile(j) >> (t % 6)) & 1

assert profile(0) == 42 and profile(1) == 44
for j in range(84):
    assert cycle[(origin-j) % 84] % 64 == profile(j+1)
failures = []
for t in range(6):
    for j in range(84):
        actual = cell(t+1, j)
        expected = cell(t, j-1) ^ (cell(t, j) | cell(t, j+1))
        if actual != expected:
            failures.append([t, j, actual, expected])
assert not failures

def periodic_column(j, p):
    return all(cell(t+p, j) == cell(t, j) for t in range(6))
assert periodic_column(0, 2) and not periodic_column(0, 1)
assert periodic_column(1, 6)
assert all(not periodic_column(1, p) for p in (1,2,3))
assert cell(1,1) == 0 and cell(5,1) == 1
assert all(cell(t+6,j) == cell(t,j) for t in range(6) for j in range(84))

# Exact support/period checks of the single named symbolic row; no evolution.
initial = [cell(0,j) for j in range(84)]
assert any(initial)
assert all(any(initial[(j+d)%84] != initial[j] for j in range(84))
           for d in (1,2,3,4,6,7,12,14,21,28,42))

result = {
    'status': 'PASS',
    'input': '../physical-ring-column-period-20261027T0730/INVERSE-RESULT.json',
    'input_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'validation': 'Only the saved candidate: no graph search or trajectory evolution',
    'physical_spacetime': 'X(t,j)=bit(t mod 6, floor(cycle[(8-j) mod 84]/64))',
    'physical_stencils_checked': 504,
    'pair_overlap_checks': 84,
    'failed_stencils': failures,
    'center_time_word': [cell(t,0) for t in range(6)],
    'right_time_word': [cell(t,1) for t in range(6)],
    'left_time_word': [cell(t,-1) for t in range(6)],
    'least_center_period': 2,
    'least_right_period': 6,
    'least_global_time_period': 6,
    'least_spatial_period': 84,
    'not_2P_witness': {'column': 1, 'time': 1, 'shift': 4, 'before': 0, 'after': 1},
    'scope': 'Full physical bi-infinite periodic orbit; initial support is infinite, not a finite-seed counterexample',
    'kernel_checked': False,
}
(phase / 'CYCLE-AUDIT.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(json.dumps(result, indent=2))
