"""One fixed finite scalar cone, authorized in PROTOCOL.md; no search."""
from functools import lru_cache
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
prior = root.parent / 'period5-carrier-defect-20261027T0820'
def gate(r):
    return int(r % 5 == 0) if r <= 0 else int((r - 3) % 5 == 0)
def boundary(t):
    return 1 - gate(t // 2) if t % 2 == 0 else 1

lo, hi, depth = -25, 31, 32
rows = [[0] * (hi - lo + 1), [boundary(t) for t in range(lo, hi + 1)]]
for k in range(1, depth):
    old, current = rows[k - 1], rows[k]
    rows.append([current[i + 1] ^ (current[i] | old[i])
                 for i in range(len(current) - 1)])

@lru_cache(None)
def scalar(k, t):
    if k == 0:
        return False
    if k == 1:
        return bool(boundary(t))
    return scalar(k - 1, t + 1) != (scalar(k - 1, t) or scalar(k - 2, t))

packet = []
for t in range(-25, 1):
    A, B = rows[31][t - lo], rows[32][t - lo]
    assert A == int(scalar(31, t)) and B == int(scalar(32, t))
    packet.append({'t': t, 'A': A, 'B': B, 'shifted_boundary': boundary(t + 2),
                   'delta': B ^ boundary(t + 2), 'L': A & (1 - B)})

carrier = json.loads((prior / 'RESULT.json').read_text(encoding='utf-8'))
B0, A0 = carrier['carrier']['pairs'][31]
mask = 1023
shift2 = lambda a: ((a >> 2) | ((a & 3) << 8)) & mask
assert (B0, A0) == (767, 682)
assert B0 == shift2(1022) and A0 & (mask ^ B0) == 0

# Outside the extracted interval these two packets are zero by the locality
# proof in PROTOCOL/PAPER, not by extrapolation from the finite cone.
delta = {r['t']: r['delta'] for r in packet}
forcing = {r['t']: r['L'] for r in packet}
residual = [t for t in range(-26, 1)
            if delta.get(t + 1, 0) ^ delta.get(t, 0) ^ forcing.get(t, 0)]
old = json.loads((prior / 'DEFECT-RESULT.json').read_text(encoding='utf-8'))
record = next(r for r in old['discrepancies'] if r['base_depth'] == 2)
assert residual == record['positions']

out = {'status': 'EXACT_FIXED_PACKET_SCALAR_PASS_NOT_LEAN',
       'cone': {'initial_times': [lo, hi], 'maximum_depth': depth,
                'extracted_times': [-25, 0]},
       'full_support_bound_from_paper_locality': [-25, 0],
       'packet': packet,
       'delta_support': [r['t'] for r in packet if r['delta']],
       'forcing_support': [r['t'] for r in packet if r['L']],
       'shear_convention': 'u=t+2; Btilde(u)=X32(u-2)',
       'sheared_delta_support': [r['t'] + 2 for r in packet if r['delta']],
       'sheared_forcing_support': [r['t'] + 2 for r in packet if r['L']],
       'odd_black_shape_failures': [r['t'] + 2 for r in packet if (r['t'] + 2) % 2 and not r['B']],
       'checks': {'recursive_scalar_cell_comparisons': 52,
                  'saved_carrier_pair_and_shield': True,
                  'saved_base_depth2_residual_exact': True},
       'scope': 'One prescribed admissible phase defect; not the actual empty gate or a finite-left witness.',
       'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(root / 'PACKET.json').write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: v for k, v in out.items() if k != 'packet'}, indent=2))
