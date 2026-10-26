"""Falsify finite backward closure while retaining left edge AND zero sensor.

Exact finite diagnostics, not a proof of P1 or an all-time witness.
"""
from pathlib import Path
from collections import deque
import hashlib
import json
import time

ROOT = Path(__file__).resolve().parent

def F(a):
    # Bit k is physical position k-age, so both edges advance in this encoding.
    return (a << 2) ^ ((a << 1) | a)

def D(a, b, h):
    return (h << 2) ^ ((h << 1) & ~b) ^ (h & ~(a << 1))

def W(delta, h):
    return (delta & (h >> 1)) ^ ((delta >> 1) & h)

def analyze(T, gap, rows, cap=10):
    witnesses = []
    per_h = {}
    a0 = rows[T]
    for H in range(1, cap+1):
        allowed = []
        for q in range(2*H+3, min(gap, 128)+1):
            V = T-q
            if V not in rows:
                continue
            ca = [(rows[T+t] >> (T+t)) & 1 for t in range(H+1)]
            cb = [(rows[V+t] >> (V+t)) & 1 for t in range(H+1)]
            if ca != cb:
                continue
            a, b = a0, rows[V] << q
            delta = a ^ b
            pulse = 1 << (2*T)
            h = delta ^ pulse
            assert h & 1 and not (h & ~delta) and not W(delta, h)
            # Independently track the added pulse and the full auxiliary field.
            for t in range(H+1):
                assert a == rows[T+t] and b == rows[V+t] << q
                assert h == (a ^ b ^ pulse)
                assert not W(a ^ b, h)
                assert not ((h >> (T+t)) & 1)
                assert h & 1  # physical leftmost position is -T-t
                if t < H:
                    h = D(a, b, h)
                    pulse = D(a, b, pulse)
                    a, b = F(a), F(b)
            # A finite preimage of pulse is unique. Force its first q+1 bits
            # from the older right front. At depth q, both prior backgrounds
            # are black, so a subset preimage of h would have to be zero.
            ap, bp = rows[T-1], rows[V-1] << q
            previous = [1, 1]
            for j in range(2, q+1):
                aj1 = (ap >> (2*(T-1)-(j-1))) & 1
                bj2 = (bp >> (2*(T-1)-(j-2))) & 1
                previous.append(((1 ^ bj2) & previous[-1]) ^ ((1 ^ aj1) & previous[-2]))
            aq = (ap >> (2*(T-1)-q)) & 1
            bq = (bp >> (2*(T-1)-q)) & 1
            assert previous[q] == 1 and aq == bq == 1
            record = {'U': T, 'V': V, 'H': H, 'gap': q,
                      'older_right_white_gap': gap, 'center_prefix': ca,
                      'left_edge_retained': True, 'zero_center_through_H': True,
                      'D_and_W_through_H': True, 'initial_subset': True,
                      'subset_previous_lift_impossible': True,
                      'forced_prior_depth': q, 'prior_delta_bit': 0,
                      'forced_prior_h_bit': 1}
            allowed.append(record)
        if allowed:
            per_h[str(H)] = len(allowed)
            witnesses.append(allowed[0])
    return per_h, witnesses

def main():
    started = time.monotonic()
    maximum_e = 19
    keep = 180
    window = deque(maxlen=keep)
    a = 1
    summaries = []
    examples = {}
    for age in range((1 << maximum_e)+11):
        window.append((age, a))
        # At T+10 the complete finite observation window is available.
        T = age-10
        if T >= 64 and T & (T-1) == 0:
            rows = dict(window)
            older = rows[T]
            next_depth = 2*T - ((older ^ (1 << (2*T))).bit_length()-1)
            white_gap = next_depth-1
            counts, found = analyze(T, white_gap, rows)
            summaries.append({'U': T, 'right_white_gap': white_gap, 'counts_by_H': counts})
            for record in found:
                examples.setdefault(str(record['H']), record)
            print(json.dumps(summaries[-1]), flush=True)
        a = F(a)
    result = {'finite_only': True, 'Lean_verified': False, 'full_problem_solved': False,
              'target': 'finite closure with canonical ancestry, subset, W, left edge and zero center',
              'maximum_dyadic_exponent': maximum_e, 'summaries': summaries,
              'smallest_older_age_examples_by_H': examples,
              'seconds': round(time.monotonic()-started, 3),
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'reset-sensor-probe.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['summaries','smallest_older_age_examples_by_H']}), flush=True)

if __name__ == '__main__':
    main()
