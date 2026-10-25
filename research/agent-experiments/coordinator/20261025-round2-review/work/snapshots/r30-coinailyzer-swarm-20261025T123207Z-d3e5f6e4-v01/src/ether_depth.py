"""Left-edge temporal-period agreement depth for Rule 30 from a single black cell.

Moving integer frame: Phi(a) = a XOR ((a<<1) OR (a<<2)), seed a=1.
Row t occupies bit positions 0..2t; the LEFT edge of the light cone is the
high end, so two rows are compared after aligning their high bits.

depth(t,p) = number of leading (left-edge) cells on which row t and row t-p
agree. No randomness, no model, no external data. Pure enumeration.
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
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
    rows = build(T)
    lo, hi = T // 2, T
    print("T=%d, t sampled over [%d,%d)" % (T, lo, hi))
    print("period  min_depth  max_depth  stable")
    for p in (1, 2, 3, 4, 6, 8, 12, 16, 20, 28, 32, 44, 60, 64, 128):
        if 2 * p >= hi:
            continue
        v = [depth(rows, t, p) for t in range(lo, hi)]
        mn, mx = min(v), max(v)
        print("%6d  %9d  %9d  %s" % (p, mn, mx, "yes" if mn == mx else "NO"))

if __name__ == "__main__":
    main()
