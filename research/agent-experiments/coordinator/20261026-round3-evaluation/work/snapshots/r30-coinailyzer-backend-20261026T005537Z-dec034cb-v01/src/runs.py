# Longest periodic stretch (period p <= PMAX) in the center trace of any finite row of length L.
# Rows normalized: bit 0 black, bit L-1 black; observed column c=0 (the handoff's frame).
import json, sys
PMAX = 16
def trace(a, n):
    out = bytearray(n)
    for u in range(n):
        out[u] = (a >> u) & 1
        a ^= (a << 1) | (a << 2)
    return out
def longest_run(t):
    best = (0, None, None)
    n = len(t)
    for p in range(1, PMAX + 1):
        run = 0
        for i in range(n - p):
            if t[i] == t[i + p]:
                run += 1
                if run > best[0]:
                    best = (run, p, i - run + 1)
            else:
                run = 0
    return best
res = {}
for L in range(2, int(sys.argv[1]) + 1):
    n = 8 * L + 64
    top = (0, None, None, None)
    for a in range(1 | (1 << (L - 1)), 1 << L, 2):
        if not (a >> (L - 1)) & 1:
            continue
        r, p, s = longest_run(trace(a, n))
        if r > top[0]:
            top = (r, p, s, bin(a)[2:])
    res[L] = {"max_run": top[0], "period": top[1], "start": top[2], "row": top[3], "trace_len": n}
    print(L, res[L], flush=True)
json.dump(res, open("runs.json", "w"), indent=1)
