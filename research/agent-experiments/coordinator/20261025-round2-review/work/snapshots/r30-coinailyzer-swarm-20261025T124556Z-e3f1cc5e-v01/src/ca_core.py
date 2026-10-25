"""Shared single-seed elementary-CA core (stdlib only).

Convention, fixed once and used by every script here:
  * cell(t, x) for t >= 0 and x in [-t, t]; cell(0, 0) = 1, all other cells of
    row 0 are 0 (the official single black cell).
  * new = f(left, center, right) with left = cell(t, x-1), right = cell(t, x+1).
  * Rule 30 is new = left XOR (center OR right).
  * Rows are stored as bytearrays of width 2*T+3 with index x + T + 1, so the
    one-cell margin keeps every in-cone cell, including cell(T,-T), correct.
"""


def rule_table(n):
    """Wolfram code n -> table[(p,q,r)] = bit."""
    return {(p, q, r): (n >> (4 * p + 2 * q + r)) & 1
            for p in (0, 1) for q in (0, 1) for r in (0, 1)}


def evolve(T, n=30):
    """Rows 0..T of rule n from a single black cell, origin index T+1."""
    tab = rule_table(n)
    W = 2 * T + 3
    row = bytearray(W)
    row[T + 1] = 1
    rows = [row]
    for _ in range(T):
        prev = rows[-1]
        nxt = bytearray(W)
        for i in range(1, W - 1):
            nxt[i] = tab[(prev[i - 1], prev[i], prev[i + 1])]
        rows.append(nxt)
    return rows


def column(rows, x, T):
    """Fixed column x as a list over t = 0 .. len(rows)-1."""
    return [rows[t][x + T + 1] for t in range(len(rows))]


def is_left_permutive(n):
    """f(0,q,r) != f(1,q,r) for every (q,r): the left variable is invertible."""
    tab = rule_table(n)
    return all(tab[(0, q, r)] != tab[(1, q, r)] for q in (0, 1) for r in (0, 1))


def black_left_edge(rows, T, upto=None):
    """cell(t,-t) == 1 for every t in 0..upto."""
    upto = len(rows) - 1 if upto is None else upto
    return all(rows[t][T + 1 - t] == 1 for t in range(upto + 1))


def eventual_period(seq, max_period, max_transient):
    """Smallest (transient, period) with seq[t+P] == seq[t] for all t >= T0,
    searched over the finite prefix only. Returns None if none found."""
    L = len(seq)
    best = None
    for P in range(1, max_period + 1):
        for T0 in range(0, max_transient + 1):
            if T0 + P >= L:
                break
            if all(seq[t + P] == seq[t] for t in range(T0, L - P)):
                if best is None or P < best[1]:
                    best = (T0, P)
                break
    return best
