import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
from density_floor import exact_density
t0 = time.time()
best = None
hits = {}
maxL = int(sys.argv[1])
for L in range(0, maxL + 1, 2):
    d, p, blk = exact_density([L], 12 * L + 2000, maxp=1200)
    if d is None:
        continue
    hits.setdefault(d, []).append(L)
    if best is None or d < best[0]:
        best = (d, L, p, blk)
        print("L=%-5d density %-8s period %-4s black %-3s  ratio_inf %s"
              % (L, d, p, blk, Fraction(3, 4) / d), flush=True)
print("---")
print("maxL %d, legal slips measured %d, elapsed %.1fs" % (maxL, sum(len(v) for v in hits.values()), time.time() - t0))
for d in sorted(hits):
    print("  density %-8s  %3d positions, first at L=%d" % (d, len(hits[d]), hits[d][0]))
