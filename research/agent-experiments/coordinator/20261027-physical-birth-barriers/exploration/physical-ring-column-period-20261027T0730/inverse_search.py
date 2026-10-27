from pathlib import Path
import hashlib
import json
import math
import time

ROOT = Path(__file__).resolve().parent
START = time.monotonic()


def least_period(a, k):
    for p in range(1, k + 1):
        if k % p == 0 and all(((a >> t) & 1) == ((a >> ((t + p) % k)) & 1)
                             for t in range(k)):
            return p
    raise AssertionError


records = []
candidate = None
status = 'bounded_no_counterexample'
for k in range(1, 10):
    m = (1 << k) - 1
    count = 1 << (2 * k)
    seen = bytearray(count)
    periods = [least_period(a, k) for a in range(1 << k)]
    def nxt(x):
        a, b = x >> k, x & m
        u = (a >> 1) | ((a & 1) << (k - 1))
        return ((u ^ (a | b)) << k) | a
    record = dict(clock=k, states=count, visited=0, cycles=0,
                  cyclic_points=0, complete=False, global_period_histogram={})
    for seed in range(count):
        if time.monotonic() - START > 45:
            status = 'time_guard_stop'
            break
        if seen[seed]:
            continue
        local = {}
        path = []
        x = seed
        while not seen[x] and x not in local:
            local[x] = len(path)
            path.append(x)
            x = nxt(x)
        if x in local:
            cyc = path[local[x]:]
            record['cycles'] += 1
            record['cyclic_points'] += len(cyc)
            gp = math.lcm(*(periods[s >> k] for s in cyc))
            hist = record['global_period_histogram']
            hist[str(gp)] = hist.get(str(gp), 0) + 1
            for j, s in enumerate(cyc):
                a, b = s >> k, s & m
                p = periods[a]
                if p > 1 and (2 * p) % gp:
                    for h, state in enumerate(cyc):
                        center, right = state >> k, state & m
                        following = cyc[(h + 1) % len(cyc)]
                        left = following >> k
                        assert following & m == center
                        assert right == cyc[(h - 1) % len(cyc)] >> k
                        assert nxt(state) == following
                        for t in range(k):
                            bit = lambda v, i: (v >> (i % k)) & 1
                            assert bit(center, t + 1) == (bit(left,t) ^
                                                                         (bit(center,t) | bit(right,t)))
                    candidate = dict(clock=k, global_period=gp, spatial_period=len(cyc),
                                     column_period=p, center_profile=a, right_profile=b,
                                     right_period=periods[b], pair_index=j, cycle=cyc)
                    assert (2*p) % periods[b] != 0
                    status = 'counterexample'
                    break
        for v in path:
            seen[v] = 1
        record['visited'] += len(path)
        if candidate:
            break
    record['complete'] = record['visited'] == count
    records.append(record)
    if candidate or status == 'time_guard_stop':
        break

result = dict(status=status, elapsed_seconds=time.monotonic()-START,
              clocks=records, candidate=candidate,
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              scope='Full inverse-pair cycles: all spatial widths for each completed clock')
(ROOT / 'INVERSE-RESULT.json').write_text(json.dumps(result, indent=2)+'\n',encoding='utf-8')
summary = dict(status=status, elapsed_seconds=result['elapsed_seconds'],
               completed_clocks=[r['clock'] for r in records if r['complete']],
               cycles=sum(r['cycles'] for r in records))
if candidate:
    summary['candidate'] = {k:v for k,v in candidate.items() if k != 'cycle'}
print(json.dumps(summary))
