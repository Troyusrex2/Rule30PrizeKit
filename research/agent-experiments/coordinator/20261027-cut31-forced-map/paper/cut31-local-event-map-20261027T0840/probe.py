from pathlib import Path
from functools import lru_cache
import hashlib
import json
import time

ROOT = Path(__file__).resolve().parent
start = time.monotonic()
states = [(d, g) for g in (3, 5) for d in range(g)]

def successors(state):
    d, g = state
    if d:
        return [(d - 1, g)]
    return [(h - 1, h) for h in (3, 5) if h == 5 or g == 5]

for state in states:
    reached = {state}
    while True:
        expanded = reached | {q for p in reached for q in successors(p)}
        if expanded == reached:
            break
        reached = expanded
    assert reached == set(states)

@lru_cache(None)
def words(state, length):
    if length == 0:
        return frozenset([0])
    bit = int(state[0] == 0)
    return frozenset(bit | (word << 1)
                     for nxt in successors(state)
                     for word in words(nxt, length - 1))

all_words = sorted(set().union(*(words(s, 17) for s in states)))
records = []
groups = {}
for word in all_words:
    g = [(word >> i) & 1 for i in range(17)]
    k = [g[i] & g[i + 3] for i in range(14)]
    a = sum((1 - g[t // 2] if t % 2 == 0 else 1) << t for t in range(33))
    current, older = a, 0
    remaining = 33
    for _ in range(31):
        remaining -= 1
        current, older = ((current >> 1) ^ (current | older)) & ((1 << remaining) - 1), current
    b = current & 3
    l = older & ~current & 3
    parity = lambda indices: sum(k[i] for i in indices) % 2
    predicted_b = (1 ^ g[1] ^ parity([1, 5, 7, 8, 12])) | ((1 ^ parity([3, 4, 7, 8, 11, 13])) << 1)
    predicted_l = parity([6, 7, 12]) | (parity([7, 8, 13]) << 1)
    residual = (b ^ predicted_b) | ((l ^ predicted_l) << 2)
    features = tuple(i for i in range(6) if k[i] and k[i + 8])
    entry = groups.setdefault(features, {'count': 0, 'residuals': set()})
    entry['count'] += 1
    entry['residuals'].add(residual)
    records.append({'word': word, 'B': b, 'L': l, 'isolated_B': predicted_b,
                    'isolated_L': predicted_l, 'features': list(features), 'residual': residual})

accepted = all(len(v['residuals']) == 1 for v in groups.values()) and groups[()]['residuals'] == {0}
out = {
    'status': 'EXACT_LOCAL_CORRECTION_FOUND' if accepted else 'PROPOSED_LOCAL_CORRECTION_FAILED',
    'scope': 'All17-letter words of the specified strongly connected8-state gap language; no second-reset closure claim.',
    'state_count': len(states), 'window_length': 17, 'distinct_words': len(all_words),
    'isolated_formula_failures': sum(r['residual'] != 0 for r in records),
    'groups': [{'features': list(k), 'count': v['count'], 'residuals': sorted(v['residuals'])}
               for k, v in sorted(groups.items())],
    'records': records,
    'elapsed_seconds': time.monotonic() - start,
    'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
(ROOT / 'RESULT.json').write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: v for k, v in out.items() if k != 'records'}))
