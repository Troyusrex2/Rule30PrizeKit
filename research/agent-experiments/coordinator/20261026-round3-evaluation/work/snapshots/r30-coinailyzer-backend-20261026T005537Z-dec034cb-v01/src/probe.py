# Doubled-die census probe: which finite rows have an eventually periodic center trace?
import collections, json, sys
N, T0, PMAX, L = 160, 48, 16, int(sys.argv[1]) if len(sys.argv) > 1 else 14
def trace(a, c=0):
    out = []
    for u in range(N):
        out.append((a >> (c + u)) & 1)
        a = a ^ ((a << 1) | (a << 2))
    return out
def period(t):
    for p in range(1, PMAX + 1):
        if all(t[i] == t[i + p] for i in range(T0, N - p)):
            return p
    return None
hits = collections.Counter(); ex = {}
for a in range(1, 1 << L):
    if not a & 1:          # bit 0 black = normalized right edge
        continue
    p = period(trace(a))
    if p:
        hits[p] += 1; ex.setdefault(p, []).append(bin(a)[2:]) if len(ex.get(p, [])) < 5 else None
seed = [period(trace(1 << 0)) ] 
print(json.dumps({"L": L, "rows": 1 << (L - 1), "periodic_by_p": dict(sorted(hits.items())),
                  "examples": ex, "seed_trace_periodic": seed[0]}, indent=1))
