"""Falsify the unproved edge horizon with exhaustive two-limb NumPy traces.

Finite experiments only. No NumPy result is a Lean theorem or infinite premise.
"""
import argparse
import gc
import json
from pathlib import Path
import random
import time
import numpy as np
import psutil
from inverse_trace_gap_probe import trace

HERE = Path(__file__).resolve().parent
PROCESS = psutil.Process()


def guard(start, limit=110):
    if (time.monotonic()-start > limit or PROCESS.memory_info().rss > 2*1024**3
            or psutil.virtual_memory().available < 2*1024**3):
        raise RuntimeError('resource guard; incomplete domains are not reported as complete')


def vector_traces(rows, c, h, start):
    assert 0 <= c and 0 < h <= 64 and c+h <= 128
    lo = np.asarray([a & ((1 << 64)-1) for a in rows], dtype=np.uint64) if not isinstance(rows, np.ndarray) else rows.copy()
    hi = np.asarray([a >> 64 for a in rows], dtype=np.uint64) if not isinstance(rows, np.ndarray) else np.zeros_like(lo)
    code = np.zeros_like(lo)
    for t in range(h):
        if t % 4 == 0:
            guard(start)
        i = c+t
        limb = lo if i < 64 else hi
        code <<= np.uint64(1)
        code |= (limb >> np.uint64(i % 64)) & np.uint64(1)
        # Phi's low-index bits never depend on discarded bits above index 127.
        mixed = hi << np.uint64(1)
        mixed |= lo >> np.uint64(63)
        mixed |= hi << np.uint64(2)
        mixed |= lo >> np.uint64(62)
        hi ^= mixed
        lo ^= (lo << np.uint64(1)) | (lo << np.uint64(2))
    guard(start)
    return code


def bit_reverse(word, h):
    return int(format(word, f'0{h}b')[::-1], 2)


def domain(n, c, h):
    start = time.monotonic()
    assert n <= 24 and c < n and h >= 2*n+2
    rows = np.arange(1, 1 << n, dtype=np.uint64)
    keys = vector_traces(rows, c, h, start)
    del rows
    gc.collect()
    order = np.argsort(keys, kind='stable')
    guard(start)
    # Row a is stored at ordinal a-1. All integers here are exactly represented.
    edges = (np.frexp(order.astype(np.float64)+1)[1]-1).astype(np.uint8)
    sorted_keys = keys[order]
    del keys
    different = edges[:-1] != edges[1:]
    delta = sorted_keys[:-1] ^ sorted_keys[1:]
    # The smallest XOR across an adjacent label change maximizes leading
    # agreement. Same-key conflicting labels give a finite collision.
    best_delta = int(np.min(delta, where=different, initial=np.iinfo(np.uint64).max))
    witnesses = np.flatnonzero(different & (delta == np.uint64(best_delta)))
    index = int(witnesses[0])
    a, b = int(order[index])+1, int(order[index+1])+1
    delay = h-best_delta.bit_length() if best_delta else h
    assert a.bit_length() != b.bit_length()
    direct = trace(a, c, h) ^ trace(b, c, h)
    assert direct == bit_reverse(best_delta, h)
    assert delay == ((direct & -direct).bit_length()-1 if direct else h)
    guard(start)
    return {'initial_bit_bound': n, 'center_index': c, 'horizon': h,
            'all_nonzero_rows': (1 << n)-1, 'complete_domain': True,
            'longest_different_edge_common_prefix': delay,
            'maximal_delay_witness': [a, b],
            'first_difference_time': delay if direct else None,
            'candidate_2n_plus_2_holds_on_domain': delay < 2*n+2,
            'seconds': round(time.monotonic()-start, 3)}


def controls():
    start = time.monotonic()
    rng = random.Random(302410)
    # Exercise carry across the limb boundary with arbitrary 96-bit initial rows.
    checks = 0
    for c in [0, 1, 17, 63]:
        rows = [rng.getrandbits(96) for _ in range(128)]
        keys = vector_traces(rows, c, 64, start)
        for a, key in zip(rows, keys):
            assert int(key) == bit_reverse(trace(a, c, 64), 64)
            checks += 1
    # Independently brute-force every different-edge pair on small domains.
    pairs = 0
    for n in range(3, 8):
        for c in sorted({1, n//2, n-1}):
            h = 32
            result = domain(n, c, h)
            keys = [trace(a, c, h) for a in range(1 << n)]
            longest = -1
            for a in range(1, 1 << n):
                for b in range(1, a):
                    if a.bit_length() == b.bit_length():
                        continue
                    delta = keys[a] ^ keys[b]
                    assert delta
                    longest = max(longest, (delta & -delta).bit_length()-1)
                    pairs += 1
            assert longest == result['longest_different_edge_common_prefix']
    return {'python_integer_trace_comparisons': checks,
            'naive_different_edge_pairs': pairs, 'all_passed': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--widths', type=int, nargs='+', default=[20, 22, 24])
    parser.add_argument('--centers', type=int, nargs='+', help='Override the four selected centers per width')
    parser.add_argument('--output', type=Path, default=HERE/'vector-edge-horizon-probe.json')
    args = parser.parse_args()
    if any(not 2 <= n <= 24 for n in args.widths):
        parser.error('widths must be between 2 and 24')
    if args.centers and any(not 0 <= c < n for n in args.widths for c in args.centers):
        parser.error('every center must be nonnegative and below every requested width')
    start = time.monotonic()
    checked = controls()
    print(json.dumps({'controls': checked}), flush=True)
    results = []
    stop = None
    try:
        for n in args.widths:
            for c in sorted(set(args.centers) if args.centers else {n//4, n//2, 3*n//4, n-1}):
                if time.monotonic()-start > 300:
                    raise RuntimeError('total time guard; remaining domains not tested')
                record = domain(n, c, 64)
                results.append(record)
                print(json.dumps(record), flush=True)
                if not record['candidate_2n_plus_2_holds_on_domain']:
                    raise RuntimeError('finite counterexample to the candidate horizon')
                gc.collect()
    except RuntimeError as exc:
        stop = str(exc)
    report = {'finite_experiment_only': True, 'Lean_verified': False,
              'edge_observability_proved': False, 'full_problem_solved': False,
              'numpy_version': np.__version__, 'requested_widths': args.widths,
              'requested_centers': args.centers,
              'controls': checked, 'results': results, 'stopped_reason': stop,
              'seconds': round(time.monotonic()-start, 3)}
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'completed_domains': len(results), 'stopped_reason': stop,
                      'seconds': report['seconds']}), flush=True)


if __name__ == '__main__':
    main()
