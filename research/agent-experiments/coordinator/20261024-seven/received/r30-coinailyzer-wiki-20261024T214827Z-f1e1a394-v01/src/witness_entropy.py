# -*- coding: utf-8 -*-
"""Rule 30 centre column: measure the DISCARDED witness, not the stored bit.

Seed: single black cell.  Update, with bit index i increasing to the left of the array
written as a Python integer:

    new[i] = row[i-1] XOR (row[i] OR row[i+1])

so under this representation the LEFT neighbour of cell i is the LOWER index i-1 and the
RIGHT neighbour is the HIGHER index i+1.  (Getting this backwards silently permutes the
witness alphabet; the determinism check below is what catches it.)

For the centre cell only, record

    w(t) = (l, c, r) at time t, as a 3-bit letter 0..7, l = left, c = centre, r = right

Four of the eight letters write centre = 1 and four write centre = 0, so the usual object
of study, the centre bit, is a 4-to-1 projection of w.  This script measures how much
structure survives in w that the projection destroys.

Control: one bit of w(t+1) is DETERMINED by w(t), since c(t+1) = l(t) XOR (c(t) OR r(t)).
The ceiling for H(w(t+1) | w(t)) is therefore 2 bits, not 3, and the script asserts the
link holds on every step before reporting against that ceiling.

Run:  python -I witness_entropy.py [N]
"""
import math
import sys
from collections import Counter

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass


def evolve(n):
    """Return the first n centre-cell witness letters, and the centre bits."""
    pad = n + 4
    row = 1 << pad          # single black cell at bit index pad
    ctr = pad
    mask = (1 << (2 * pad)) - 1
    bits, wit = [], []
    for _ in range(n):
        left = (row >> (ctr - 1)) & 1
        cen = (row >> ctr) & 1
        right = (row >> (ctr + 1)) & 1
        bits.append(cen)
        wit.append((left << 2) | (cen << 1) | right)
        row = (row << 1) ^ (row | (row >> 1))
        row &= mask
    return bits, wit


def entropy(counter, n):
    return -sum(v / n * math.log2(v / n) for v in counter.values())


def conditional(seq, k):
    """H(x[t+1] | x[t-k+1..t]) in bits, plug-in estimator."""
    joint = Counter(tuple(seq[i:i + k + 1]) for i in range(len(seq) - k))
    ctxt = Counter(tuple(seq[i:i + k]) for i in range(len(seq) - k))
    n = len(seq) - k
    return entropy(joint, n) - entropy(ctxt, n)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400000
    bits, wit = evolve(n)

    link = all(
        ((wit[t + 1] >> 1) & 1)
        == (((wit[t] >> 2) & 1) ^ (((wit[t] >> 1) & 1) | (wit[t] & 1)))
        for t in range(n - 1)
    )
    print("N = %d" % n)
    print("determinism link  c(t+1) = l(t) XOR (c(t) OR r(t))  holds on all %d steps: %s"
          % (n - 1, link))
    assert link, "witness orientation is wrong; l and r are swapped"

    print("centre bit: fraction of ones %.5f" % (sum(bits) / n))
    cw = Counter(wit)
    print("\nletter (l,c,r) -> centre it writes : count     share")
    for k in range(8):
        l, c, r = (k >> 2) & 1, (k >> 1) & 1, k & 1
        print("  %d%d%d -> %d : %8d   %.5f" % (l, c, r, l ^ (c | r), cw[k], cw[k] / n))

    for v in (0, 1):
        ks = [k for k in range(8)
              if (((k >> 2) & 1) ^ (((k >> 1) & 1) | (k & 1))) == v]
        tot = sum(cw[k] for k in ks)
        print("centre=%d is written by %d distinct letters, %d times; split %s"
              % (v, len(ks), tot, ["%.3f" % (cw[k] / tot) for k in ks]))

    print("\nstored column, ceiling 1 bit:")
    for k in (1, 4, 8):
        print("  H(bit(t+1) | last %d bits)     = %.4f" % (k, conditional(bits, k)))
    print("witness column, ceiling 2 bits (one bit of each letter is determined):")
    for k in (1, 2, 3, 4):
        print("  H(w(t+1)   | last %d witnesses) = %.4f" % (k, conditional(wit, k)))
    print("\nNote: the plug-in estimator is biased DOWNWARD as the context grows "
          "(8^4 = 4096 contexts at k=4). Only the k=1 witness figure is sample-robust here.")


if __name__ == "__main__":
    main()
