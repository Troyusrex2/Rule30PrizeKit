# -*- coding: utf-8 -*-
"""Exact bit-level reimplementation of the Rule30PrizeKit coupled objects.

Mirrors these official definitions (kit commit 102d5b8e, Lean sources):

  Rule30Jen.rule a b c            = xor a (b || c)
  Rule30PeriodTwoCoupled.altCol t = (t % 2 == 0)
  Rule30Ether.drv c x 0 p         = if p = 0 then c 0 else x p
  Rule30Ether.drv c x (t+1) 0     = c (t+1)
  Rule30Ether.drv c x (t+1) (p+1) = rule (drv t p) (drv t (p+1)) (drv t (p+2))
  Rule30PeriodTwoSideways.u R s   = drv altCol R (2*s+1) 1
  Rule30PeriodTwoSideways.Psi R   = Theta (fun s => !u R s)
  Rule30ZeroBoundary.alt f t      = if t % 2 = 0 then true else f (t / 2)
  Rule30ZeroBoundary.recon a 0 t  = false
  Rule30ZeroBoundary.recon a 1 t  = a t
  Rule30ZeroBoundary.recon a (k+2) t
      = xor (recon a (k+1) (t+1)) (recon a (k+1) t || recon a k t)
  Rule30ZeroBoundary.lam a k      = recon a k 0
  Rule30ZeroBoundary.Theta f      = lam (alt f)
  free R k                        = zrow (Psi R) (2*k+1) 1 = !u R k   (Psi_free)
  zeros s n                       = #{ i < n : s i = false }
  blackCount L n                  = #{ i < n : L i = true }

Rows are Python ints used as bit vectors (bit p = cell p), so every step is
exact integer arithmetic with no floating point and no truncation: the
simulated width always exceeds the true support, which spreads at speed one.

Pure Python 3, standard library only.  Run:  python -I coupled_core.py
"""
import sys

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

# --- Rule30Ether.etherTable / ether -----------------------------------------
ETHER_TABLE = [
    [0, 0, 1, 1],
    [0, 1, 1, 0],
    [1, 1, 0, 1],
    [0, 1, 0, 1],
    [0, 0, 1, 1],
    [0, 0, 0, 1],
    [0, 0, 0, 1],
]


def ether(j, phi):
    return ETHER_TABLE[j % 7][phi % 4]


# The 13-cell wall of Rule30CriticalChargeOneCoreResearch.wall.
WALL_C1 = [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0]


def config(j0, phi, k, ws):
    """Rule30Ether.config as a dict {position: bit} with finite support."""
    r = {}
    for p in range(1, k + 1):
        r[p] = ether(j0 + p, phi)
    for i, b in enumerate(ws):
        r[k + 1 + i] = b
    return {p: b for p, b in r.items() if b}


def right_mask(support):
    """Pack {position: bit} (positions >= 1) into a bit vector."""
    m = 0
    for p, b in support.items():
        if b:
            m |= 1 << p
    return m


def free_stream(rmask, n):
    """free R s for s = 0 .. n-1, as a list of 0/1 (1 = black).

    free R s = !drv altCol R (2*s+1) 1.
    """
    T = 2 * n - 1 if n > 0 else 0
    span = rmask.bit_length()
    W = span + T + 3                      # support spreads right at speed 1 only
    mask = (1 << (W + 1)) - 1
    row = rmask & mask                    # t = 0, p >= 1
    row |= 1                              # altCol 0 = true, so bit 0 is set
    out = []
    for t in range(T):
        # p >= 1 : new[p] = row[p-1] xor (row[p] or row[p+1])
        row = ((row << 1) ^ (row | (row >> 1))) & mask
        row &= ~1                         # clear p = 0, then impose the driver
        if (t + 1) % 2 == 0:
            row |= 1
        if (t + 1) % 2 == 1:              # odd time 2*s+1
            out.append(1 - ((row >> 1) & 1))
        if len(out) == n:
            break
    while len(out) < n:
        out.append(0)
    return out


def psi_row(fstream, depth):
    """Psi R d for d = 0 .. depth, from the free stream, as a list of 0/1.

    Psi R = Theta f = lam (alt f), alt f t = 1 if t even else f (t/2).
    Needs f on 0 .. depth//2, which `fstream` must cover.
    """
    K = depth                              # highest time index of `a` required
    a = 0
    for t in range(K + 1):
        bit = 1 if t % 2 == 0 else fstream[t // 2]
        if bit:
            a |= 1 << t
    out = [0]                              # recon a 0 t = false
    if depth == 0:
        return out
    r_prev = 0                             # recon a 0 (as a bit vector over t)
    r_cur = a                              # recon a 1
    out.append(r_cur & 1)
    for k in range(2, depth + 1):
        width = K - k + 1
        m = (1 << (width + 1)) - 1
        r_next = ((r_cur >> 1) ^ (r_cur | r_prev)) & m
        r_prev, r_cur = r_cur, r_next
        out.append(r_cur & 1)
    return out


def counts(rmask, n):
    """(zeros(free R, n), blackCount(Psi R, 2*n+1), free stream, Psi row)."""
    f = free_stream(rmask, n + 1)
    psi = psi_row(f, 2 * n)
    z = sum(1 for i in range(n) if f[i] == 0)
    b = sum(psi[:2 * n + 1])
    return z, b, f, psi


def excess(z, n):
    """5*zeros - n, the quantity the critical charge must pay for."""
    return 5 * z - n


def _selftest():
    """Reproduce the published C=1 witness exactly."""
    R = right_mask(config(3, 1, 6, WALL_C1))
    n = 14 * 40
    z, b, f, psi = counts(R, n)
    print("witness  Rule30Ether.config 3 1 6 wall   (0x%x)" % R)
    print("  free R, first 16      :", "".join(str(x) for x in f[:16]))
    print("  Psi R, depths 0..15   :", "".join(str(x) for x in psi[:16]))
    ok_free = all(f[s] == (1 if s % 2 == 1 else 0) for s in range(n))
    pat = [1, 1, 0, 0, 0, 0, 1]
    ok_psi = psi[0] == 0 and all(psi[d] == pat[(d - 1) % 7] for d in range(1, 2 * n + 1))
    print("  free R s == (s odd)              :", ok_free)
    print("  Psi R d>=1 == 1100001 repeated   :", ok_psi)
    for k in (1, 2, 5, 40):
        nk = 14 * k
        zk, bk, _, _ = counts(R, nk)
        print("  n = 14*%-3d  zeros = %-6d (7k = %-6d)  blackCount = %-6d (12k = %-6d)"
              % (k, zk, 7 * k, bk, 12 * k))
        assert zk == 7 * k and bk == 12 * k, "published counts not reproduced"
    assert ok_free and ok_psi, "published witness not reproduced"
    print("  excess/black ratio    : %.6f  (21k/12k = 1.75)"
          % (excess(z, n) / b))
    print("SELFTEST PASSED: the kernel-checked C=1 witness is reproduced exactly.")


if __name__ == "__main__":
    _selftest()
