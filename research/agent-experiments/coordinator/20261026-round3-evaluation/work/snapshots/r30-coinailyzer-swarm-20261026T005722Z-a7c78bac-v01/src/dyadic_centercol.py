"""Does the center column inherit the row's 2-adic structure? (It does not.)

Frame: Phi(a) = a XOR ((a<<1)|(a<<2)), seed a=1. The cone's right edge is
stationary at bit 0 and the left edge grows 2 bits per step, so the TRUE
center cell of row t sits at bit t:  c(t) = (rows[t] >> t) & 1.
Sanity: t=0 -> 1 ; t=1 -> row 7 = 111, center 1.

A companion response measured that left-edge agreement depth is a function of
v2(p) alone (8, 29, 400 for v2 = 1,2,3). This asks the obvious next question:
is the center column's own agreement density A(k) also a function of v2(k)?

A(k) = fraction of t with c(t) == c(t+k), bucketed by v2(k).
If the row's dyadic rigidity reached the center column, A would step by bucket.
"""
import collections, sys

def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2; k += 1
    return k

def main():
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 60000
    KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 512
    row, c = 1, []
    for t in range(T):
        c.append((row >> t) & 1)
        row = row ^ ((row << 1) | (row << 2))
    print("T=%d  center col starts %s" % (T, "".join(map(str, c[:24]))))
    print("density of ones: %.5f" % (sum(c) / len(c)))
    buck = collections.defaultdict(list)
    for k in range(1, KMAX + 1):
        n = T - k
        buck[v2(k)].append(sum(1 for t in range(n) if c[t] == c[t + k]) / n)
    print("v2(k)  #k      mean A      min        max")
    for v in sorted(buck):
        a = buck[v]
        print("%5d %4d   %.5f   %.5f   %.5f"
              % (v, len(a), sum(a) / len(a), min(a), max(a)))
    print("chance is 0.5; a dyadic effect would separate the buckets.")

if __name__ == "__main__":
    main()
