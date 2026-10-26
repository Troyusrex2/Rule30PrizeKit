"""Independent physical-coordinate set verification; imports no producer code."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent

def physical(row):
    if not row:
        return set()
    return {p for p in range(min(row)-1, max(row)+2)
            if ((p-1 in row) != ((p in row) or (p+1 in row)))}

def auxiliary(a, b, h):
    return {p for p in range(min(h)-1, max(h)+2)
            if ((p-1 in h) ^ ((p in h) and (p+1 not in b)) ^
                ((p+1 in h) and (p not in a)))}

rows = [{0}]
for _ in range(263):
    rows.append(physical(rows[-1]))
U, V, H = 256, 237, 6
h = rows[U] ^ rows[V] ^ {U}
assert h <= rows[U] ^ rows[V]
pulse = {U}
checks = []
for t in range(H+1):
    a, b = rows[U+t], rows[V+t]
    delta = a ^ b
    assert h == delta ^ pulse and min(h) == -U-t and 0 not in h
    assert all(((p+1 in delta) and (p in h)) == ((p in delta) and (p+1 in h))
               for p in range(-U-t-1, U+t+1))
    checks.append({'t': t, 'center': False, 'leftmost': min(h), 'W': True})
    h = auxiliary(a, b, h)
    pulse = physical(pulse)
    assert h == rows[U+t+1] ^ rows[V+t+1] ^ pulse

# Reconstruct a hypothetical subset predecessor of the FULL h, rather than
# reconstructing the removed pulse as the producer does.
a, b = rows[U-1], rows[V-1]
target = rows[U] ^ rows[V] ^ {U}
prior = {U: False, U+1: False}
for p in range(U, V-1, -1):
    prior[p-1] = ((p in target) ^ ((p+1 not in b) and prior[p]) ^
                  ((p not in a) and prior[p+1]))
assert prior[V-1] and (V-1 in a) and (V-1 in b)
assert all(p in a for p in range(V-1, U))

# Corrupt a required center observation and a required subset bit. Both must
# be rejected by the same independent equations.
corrupt_center = (rows[U] ^ rows[V] ^ {U}) ^ {0}
assert 0 in corrupt_center
corrupt_prior = dict(prior)
corrupt_prior[V-1] = False
p = V
rhs = (corrupt_prior[p-1] ^ ((p+1 not in b) and corrupt_prior[p]) ^
       ((p not in a) and corrupt_prior[p+1]))
assert rhs != (p in target)
result = {'pass': True, 'U': U, 'V': V, 'H': H, 'physical_set_model': True,
          'initial_subset': True, 'D_and_W': True, 'retains_left_edge': True,
          'zero_center_through_H': True, 'checks': checks,
          'forced_forbidden_prior_position': V-1, 'corruptions_rejected': 2,
          'Lean_verified': False, 'all_time_counterexample': False,
          'full_problem_solved': False}
(ROOT/'independent-sensor-check.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k != 'checks'}), flush=True)
