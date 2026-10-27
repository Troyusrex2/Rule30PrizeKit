"""Only the authorized starts0,8 control, compared to the frozen one packet."""
from functools import lru_cache
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
single = json.loads((root / 'PACKET.json').read_text(encoding='utf-8'))
assert single['source_sha256'] == 'c1bd5f2dec819ad85f3b4a553399fa46782df675b0d07510929bb2f93c4cd6bb'
assert hashlib.sha256((root / 'extract_packet.py').read_bytes()).hexdigest() == single['source_sha256']
def gate(r):
    if r <= 0:
        return int(r % 5 == 0)
    if r <= 8:
        return int((r - 3) % 5 == 0)
    return int((r - 11) % 5 == 0)
def boundary(t):
    return 1 - gate(t // 2) if t % 2 == 0 else 1

lo, hi = -25, 47
rows = [[0] * (hi - lo + 1), [boundary(t) for t in range(lo, hi + 1)]]
for k in range(1, 32):
    old, cur = rows[k - 1], rows[k]
    rows.append([cur[i + 1] ^ (cur[i] | old[i]) for i in range(len(cur) - 1)])
@lru_cache(None)
def scalar(k, t):
    if k == 0:
        return False
    if k == 1:
        return bool(boundary(t))
    return scalar(k - 1, t + 1) != (scalar(k - 1, t) or scalar(k - 2, t))

d = {r['t']: r['delta'] for r in single['packet']}
f = {r['t']: r['L'] for r in single['packet']}
packet = []
for t in range(-25, 17):
    A, B = rows[31][t - lo], rows[32][t - lo]
    assert A == int(scalar(31, t)) and B == int(scalar(32, t))
    delta, forcing = B ^ boundary(t + 2), A & (1 - B)
    dsum, fsum = d.get(t, 0) ^ d.get(t - 16, 0), f.get(t, 0) ^ f.get(t - 16, 0)
    packet.append({'t': t, 'A': A, 'B': B, 'delta': delta, 'L': forcing,
                   'single_delta_sum': dsum, 'single_forcing_sum': fsum,
                   'delta_interaction': delta ^ dsum, 'forcing_interaction': forcing ^ fsum})
ds = [r['t'] for r in packet if r['delta_interaction']]
ls = [r['t'] for r in packet if r['forcing_interaction']]
assert all(-9 <= t <= 0 for t in ds + ls)
out = {'status': 'ONE_ADJACENT_PAIR_SCALAR_PASS_NOT_LEAN',
       'short_starts_gate_indices': [0, 8], 'physical_translations': [0, 16],
       'cone': {'initial_times': [lo, hi], 'max_depth': 32, 'extracted_times': [-25, 16]},
       'delta_interaction_support': ds, 'forcing_interaction_support': ls,
       'interaction_parity_counts': {
           'delta_even': sum(t % 2 == 0 for t in ds), 'delta_odd': sum(t % 2 == 1 for t in ds),
           'L_even': sum(t % 2 == 0 for t in ls), 'L_odd': sum(t % 2 == 1 for t in ls)},
       'packet': packet, 'independent_scalar_comparisons': 84,
       'scope': 'One admissible two-defect control; no uniform formula follows without the separate locality proof.',
       'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(root / 'TWO-PACKET.json').write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: v for k, v in out.items() if k != 'packet'}, indent=2))
