"""Bounded strip vs positive-density regular region, by 2-adic valuation.

For v2(p) <= 3 the left-edge agreement depth is a constant independent of t.
For v2(p) >= 4 it is a constant FRACTION of the light cone (2t+1).
This script reports both readings so the transition is visible.
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

def main():
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    rows = build(T)
    ts = [t for t in (1000, 2000, 4000, 6000, T - 1) if t < T]
    print("T=%d" % T)
    print("   p  " + "".join("  t=%-5d depth  frac" % t for t in ts))
    for p in (4, 8, 16, 32, 64, 128):
        line = "%4d  " % p
        for t in ts:
            d = depth(rows, t, p)
            line += "  %11d %5.3f" % (d, d / (2 * t + 1))
        print(line)

if __name__ == "__main__":
    main()
