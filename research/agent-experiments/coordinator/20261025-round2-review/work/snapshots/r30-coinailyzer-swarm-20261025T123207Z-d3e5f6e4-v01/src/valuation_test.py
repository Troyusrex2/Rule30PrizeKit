"""Is left-edge agreement depth a function of v2(p) alone, not of p?

Same frame as ether_depth.py. For each period p we report v2(p), the min and
max depth over a sampled t-range, and whether it is constant in t.
"""
import sys

def build(T):
    row, rows = 1, []
    for _ in range(T):
        rows.append(row)
        row = row ^ ((row << 1) | (row << 2))
    return rows

def depth(rows, t, p):
    a, b = rows[t], rows[t - p]
    la, lb = a.bit_length(), b.bit_length()
    if la >= lb:
        b <<= (la - lb); L = la
    else:
        a <<= (lb - la); L = lb
    x = a ^ b
    return L if x == 0 else L - x.bit_length()

def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2; k += 1
    return k

def main():
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
    rows = build(T)
    lo, hi = T // 2, T
    print("T=%d, t over [%d,%d)" % (T, lo, hi))
    print("  p   v2(p)  min_depth  max_depth  constant_in_t")
    for p in (2,6,10,14, 4,12,20,28,36,44, 8,24,40,56,72, 16,48,80, 32,96):
        v = [depth(rows, t, p) for t in range(lo, hi)]
        mn, mx = min(v), max(v)
        print("%4d  %5d  %9d  %9d  %s" % (p, v2(p), mn, mx, "yes" if mn == mx else "NO"))

if __name__ == "__main__":
    main()
