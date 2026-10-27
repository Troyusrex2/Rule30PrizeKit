from pathlib import Path
import hashlib
import json
import time

ROOT = Path(__file__).resolve().parent
START = time.monotonic()
LIMIT = 45.0


def step(x, n):
    mask = (1 << n) - 1
    left = ((x << 1) | (x >> (n - 1))) & mask
    right = (x >> 1) | ((x & 1) << (n - 1))
    return left ^ (x | right)


def scalar_step(x, n):
    result = 0
    for i in range(n):
        l = (x >> ((i - 1) % n)) & 1
        c = (x >> i) & 1
        r = (x >> ((i + 1) % n)) & 1
        result |= (l ^ (c | r)) << i
    return result


def period(bits):
    pi = [0] * len(bits)
    for i in range(1, len(bits)):
        j = pi[i - 1]
        while j and bits[i] != bits[j]:
            j = pi[j - 1]
        if bits[i] == bits[j]:
            j += 1
        pi[i] = j
    p = len(bits) - pi[-1]
    return p if len(bits) % p == 0 else len(bits)


for n in range(1, 8):
    for x in range(1 << n):
        assert step(x, n) == scalar_step(x, n)
assert period([0, 1] * 3) == 2
assert period([0, 0, 1] * 2) == 3
assert period([0, 0, 1, 1]) == 4

widths = []
candidate = None
weak_controls = []
status = 'bounded_no_counterexample'
for n in range(1, 17):
    seen = bytearray(1 << n)
    record = dict(width=n, states=1 << n, visited=0, cycles=0,
                  cycle_histogram={}, nonuniform_cycles=0, complete=False)
    for seed in range(1 << n):
        if time.monotonic() - START > LIMIT:
            status = 'time_guard_stop'
            break
        if seen[seed]:
            continue
        path = []
        local = {}
        x = seed
        while not seen[x] and x not in local:
            local[x] = len(path)
            path.append(x)
            x = step(x, n)
        if x in local:
            cyc = path[local[x]:]
            k = len(cyc)
            assert step(cyc[-1], n) == cyc[0]
            record['cycles'] += 1
            hist = record['cycle_histogram']
            hist[str(k)] = hist.get(str(k), 0) + 1
            columns = [[(v >> i) & 1 for v in cyc] for i in range(n)]
            periods = [period(b) for b in columns]
            for b, p in zip(columns, periods):
                assert k % p == 0 and all(b[t] == b[(t + p) % k] for t in range(k))
            if len(set(periods)) != 1:
                record['nonuniform_cycles'] += 1
                if len(weak_controls) < 5:
                    weak_controls.append(dict(width=n, global_period=k,
                                              periods=periods, cycle=cyc))
            for i, p in enumerate(periods):
                if p > 1 and (2 * p) % k != 0:
                    assert all(scalar_step(v, n) == cyc[(t + 1) % k]
                               for t, v in enumerate(cyc))
                    candidate = dict(width=n, global_period=k, column=i,
                                     column_period=p, column_periods=periods,
                                     cycle=cyc, column_word=columns[i])
                    status = 'counterexample'
                    break
        for v in path:
            seen[v] = 1
        record['visited'] += len(path)
        if candidate:
            break
    record['complete'] = record['visited'] == record['states']
    widths.append(record)
    if candidate or status == 'time_guard_stop':
        break

result = dict(status=status, elapsed_seconds=time.monotonic()-START,
              widths=widths, candidate=candidate, weak_controls=weak_controls,
              scope='Exact spatially periodic physical orbits; not finite seeds',
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(ROOT / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
summary = dict(status=status, elapsed_seconds=result['elapsed_seconds'],
               completed_widths=[r['width'] for r in widths if r['complete']],
               cycles=sum(r['cycles'] for r in widths),
               nonuniform_cycles=sum(r['nonuniform_cycles'] for r in widths))
if candidate:
    summary['candidate'] = {k:v for k,v in candidate.items()
                            if k not in ('cycle', 'column_word')}
print(json.dumps(summary))
