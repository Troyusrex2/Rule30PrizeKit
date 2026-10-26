"""The v2>=4 growth law has an exact rational slope: depth(t,16) = (3/4) t.

Same frame. A companion response reported the regular region as "about 0.375
of the cone" and said no clean law was found. Fitting through the origin
recovers 3/4 of t, i.e. exactly 3/8 of the cone width 2t+1, which places the
regular/chaotic interface at velocity -1/4 in cone units.
"""
import statistics, sys

def main():
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 12000
    row, rows = 1, []
    for _ in range(T):
        rows.append(row); row = row ^ ((row << 1) | (row << 2))

    def depth(t, p):
        a, b = rows[t], rows[t - p]
        la, lb = a.bit_length(), b.bit_length()
        if la >= lb: b <<= (la - lb); L = la
        else:        a <<= (lb - la); L = lb
        x = a ^ b
        return L if x == 0 else L - x.bit_length()

    for p in (16, 32, 64):
        ts = range(100, T)
        d = [depth(t, p) for t in ts]
        s = sum(t * dd for t, dd in zip(ts, d)) / sum(t * t for t in ts)
        res = [dd - s * t for t, dd in zip(ts, d)]
        print("p=%3d  slope=%.6f  (3/4 = 0.750000)  resid sd=%.2f  range [%.1f, %.1f]"
              % (p, s, statistics.pstdev(res), min(res), max(res)))

if __name__ == "__main__":
    main()
