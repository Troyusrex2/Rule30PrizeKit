"""R2-03 exact finite experiments. Standard library only; no proof claim."""
import hashlib
import itertools
import json
import random
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else HERE
OUT.mkdir(parents=True, exist_ok=True)
START = time.monotonic()

def phi(a):
    return a ^ ((a << 1) | (a << 2))

def linear(a):
    return a ^ (a << 1) ^ (a << 2)

def nonlinear(a):
    return (a & (a >> 1)) << 2

def step_rule(a, rule):
    mask = (1 << (a.bit_length() + 2)) - 1
    left, center, right = a, a << 1, a << 2
    result = 0
    for triple in range(8):
        if (rule >> triple) & 1:
            result |= ((left if triple & 4 else ~left) &
                       (center if triple & 2 else ~center) &
                       (right if triple & 1 else ~right) & mask)
    return result

def physical(seed, rule, steps):
    row = {i: 1 for i in seed}
    output = []
    for t in range(steps + 1):
        output.append(row.get(0, 0))
        lo, hi = min(row, default=0)-1, max(row, default=0)+1
        row = {p: 1 for p in range(lo, hi+1)
               if (rule >> ((row.get(p-1, 0) << 2) |
                            (row.get(p, 0) << 1) | row.get(p+1, 0))) & 1}
    return output

def center_trace(rule, last):
    a = 1
    result = []
    for t in range(last+1):
        result.append((a >> t) & 1)
        a = phi(a) if rule == 30 else step_rule(a, rule)
    return result

def rank_certificate(rows, width):
    original = rows[:]
    work = [(r, i) for i, r in enumerate(rows)]
    rank = 0
    pr, pc = [], []
    for col in range(width):
        pivot = next((i for i in range(rank, len(work))
                      if (work[i][0] >> col) & 1), None)
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        pr.append(work[rank][1]); pc.append(col)
        for i in range(rank+1, len(work)):
            if (work[i][0] >> col) & 1:
                work[i] = (work[i][0] ^ work[rank][0], work[i][1])
        rank += 1
    minor = [sum(((original[i] >> j) & 1) << k for k, j in enumerate(pc))
             for i in pr]
    # Independently invert the selected minor; verify its product with the inverse.
    aug = [v | (1 << (rank+i)) for i, v in enumerate(minor)]
    for c in range(rank):
        k = next(i for i in range(c, rank) if (aug[i] >> c) & 1)
        aug[c], aug[k] = aug[k], aug[c]
        for i in range(rank):
            if i != c and ((aug[i] >> c) & 1): aug[i] ^= aug[c]
    inv = [a >> rank for a in aug]
    for i, row in enumerate(minor):
        product = 0
        for j in range(rank):
            if (row >> j) & 1: product ^= inv[j]
        assert product == 1 << i
    return {'rank': rank, 'pivot_rows': pr, 'pivot_columns': pc,
            'minor_rows_lsb_first': [''.join(str((v >> j) & 1) for j in range(rank)) for v in minor]}

def matrix(trace, n, start, k):
    assert 2**k > start+n-1
    return [sum((trace[start+i+(1 << (k+j))] ^ trace[start+i]) << j
                for j in range(n)) for i in range(n)]

def power_linear(a, n):
    # Frobenius fast powering in GF(2)[x], exact.
    k = 0
    while n:
        if n & 1: a = a ^ (a << (1 << k)) ^ (a << (2 << k))
        k += 1; n >>= 1
    return a

def control():
    for a in range(1024):
        assert phi(a) == step_rule(a, 30) == linear(a) ^ nonlinear(a)
    for rule in (30, 90, 150, 210):
        assert physical({0}, rule, 192) == center_trace(rule, 192)
    rng = random.Random(300325)
    for _ in range(128):
        a, n = rng.randrange(1024), rng.randrange(32)
        repeated = a
        for __ in range(n): repeated = linear(repeated)
        assert repeated == power_linear(a, n)
    return {'truth_table_all_10_bit_rows': 1024,
            'independent_physical_center_steps_per_rule': 193,
            'rules': [30, 90, 150, 210], 'fast_linear_power_checks': 128}

def bounded_rank_witness(trace, bound):
    length = 2*(bound+1)+1
    seen = {}
    # Enough positions to force a repeat, regardless of the center sequence.
    for t in range(2**length+1):
        word = tuple(trace[t:t+length])
        assert len(word) == length
        if word in seen:
            first = seen[word]; period = t-first
            seedrows = [1]
            for _ in range(t+length): seedrows.append(phi(seedrows[-1]))
            a, b, c = seedrows[first] << period, seedrows[t], t
            states = []
            for j in range(bound+1):
                aa, bb = a, b
                pair = []
                for u in range(3):
                    pair.append([(aa >> (c+u)) & 1, (bb >> (c+u)) & 1])
                    aa, bb = phi(aa), phi(bb)
                assert all(x == y for x, y in pair)
                assert a > 0 and a % 2 == 0 and b & 1
                assert ((b >> 1) & 1) == ((b >> 2) & 1)
                assert b.bit_length() > a.bit_length()
                states.append({'time': first+2*j, 'a': str(a), 'b': str(b),
                               'center': c, 'paired_observations': pair})
                a, b, c = phi(phi(a)), phi(phi(b)), c+2
            return {'score_bound': bound, 'T': first, 'P': period,
                    'matched_length': length, 'word': ''.join(map(str, word)),
                    'required_strict_drops': bound+1, 'states': states}
        seen[word] = t
    raise AssertionError('Pigeonhole failed')

def block_checks(trace):
    rows = [1]
    for _ in range(1024): rows.append(phi(rows[-1]))
    count = 0
    cancellation = None
    # General q=P*2^k specialization, not only powers of two.
    for t in range(32):
        for k in range(7):
            if 2**k <= t: continue
            for p in range(1, 9):
                q = p*2**k
                if t+q > 1024: continue
                total = 0; contrib = []
                for j in range(q):
                    term = power_linear(nonlinear(rows[t+j]), q-1-j)
                    total ^= term
                    if (term >> (t+q)) & 1: contrib.append(j)
                assert rows[t+q] == power_linear(rows[t], q) ^ total
                bit = (total >> (t+q)) & 1
                assert bit == trace[t+q] ^ trace[t]
                if cancellation is None and bit == 0 and contrib:
                    cancellation = {'t': t, 'k': k, 'P': p, 'q': q,
                        'coefficient_index': t+q, 'nonzero_time_contributions': contrib,
                        'contribution_count': len(contrib), 'parity': 0}
                count += 1
    return {'cases': count, 'first_cancelled_nonempty_sum': cancellation}

def ether_controls():
    # Official 7x4 ether table, physical positions left to right.
    cols = ['0011', '0110', '1101', '0101', '0011', '0001', '0001']
    states = [[int(cols[p][t]) for p in range(7)] for t in range(4)]
    def lin(a): return [a[(p-1)%7] ^ a[p] ^ a[(p+1)%7] for p in range(7)]
    def nl(a): return [a[p] & a[(p+1)%7] for p in range(7)]
    for t in range(4):
        new = [(30 >> ((states[t][(p-1)%7] << 2) | (states[t][p] << 1) | states[t][(p+1)%7])) & 1 for p in range(7)]
        assert new == states[(t+1)%4]
    terms = []
    for j in range(28):
        term = nl(states[j%4])
        for _ in range(27-j): term = lin(term)
        terms.append(term)
    total = [sum(v[p] for v in terms) % 2 for p in range(7)]
    evolved = states[0]
    for _ in range(28): evolved = lin(evolved)
    assert total == [0]*7 and evolved == states[0]
    # Independently simulate the finite right half from CRITICAL-CHARGE-ONE.
    r = 0x6b70; free = []
    scalar = {p: 1 for p in range(1, 16) if (r >> (p-1)) & 1}
    for t in range(1024):
        if t < 128:
            assert r == sum(1 << (p-1) for p in scalar)
            scalar = {p: 1 for p in range(1, max(scalar, default=1)+2)
                      if (30 >> (((int(t % 2 == 0) if p == 1 else scalar.get(p-1,0)) << 2)
                                 | (scalar.get(p,0) << 1) | scalar.get(p+1,0))) & 1}
        if t % 2: free.append(1 ^ (r & 1))
        r = (r << 1) ^ (r | (r >> 1)) ^ int(t % 2 == 0)
    assert free == [i % 2 for i in range(512)]
    rank_free = rank_certificate(matrix(free, 5, 0, 4), 5)
    assert rank_free['rank'] == 0
    return {'ether_rule_table_checks': 28, 'ether_28_step_source_total': total,
            'ether_nonzero_time_terms_by_column': [sum(v[p] for v in terms) for p in range(7)],
            'finite_right_hex': '0x6b70', 'driven_steps': 1024,
            'independent_scalar_right_rows': 128,
            'free_bits_checked': 512, 'free_prefix': ''.join(map(str, free[:32])),
            'free_difference_matrix': rank_free,
            'scope': 'Driven/Psi free-stream control only, not a single-seed full-row identity. No unbounded kernel replay.'}

def main():
    result = {'controls': control()}
    # Largest n=12 family needs c(32779), no truncation of any evolving row.
    trace = center_trace(30, 32779)
    a = 1
    for t, bit in enumerate(trace):
        assert bit == (a >> t) & 1
        a = step_rule(a,30)
    result['full_trace_truth_table_crosscheck'] = len(trace)
    (OUT/'center.bits').write_text(''.join(map(str, trace))+'\n', encoding='ascii')
    result['center_bits'] = len(trace)
    result['center_sha256'] = hashlib.sha256((OUT/'center.bits').read_bytes()).hexdigest()
    result['bounded_rank_witnesses'] = [bounded_rank_witness(trace, b) for b in (1,2,3)]
    result['block_identity'] = block_checks(trace)
    result['ether'] = ether_controls()
    result['square_family'] = []
    for n in range(1,13):
        k = (n-1).bit_length()
        rows = matrix(trace, n, 0, k)
        result['square_family'].append({'n': n, 'K': k, 'start': 0,
            'rows_lsb_first': [''.join(str((r >> j)&1) for j in range(n)) for r in rows],
            **rank_certificate(rows, n)})
    # An explicit attempt at time-monotonicity, within the q>last-row condition.
    for n in (2,3,4):
        k = 8
        prev = None
        for t in range(256-n):
            rank = rank_certificate(matrix(trace,n,t,k),n)['rank']
            if prev is not None and rank < prev[1]:
                result['time_monotonicity_failure'] = {'n': n, 'K': k,
                    'before_T':prev[0], 'before_rank':prev[1], 'after_T':t,'after_rank':rank,
                    'before_rows':matrix(trace,n,prev[0],k),'after_rows':matrix(trace,n,t,k)}
                break
            prev = (t,rank)
        if 'time_monotonicity_failure' in result: break
    # Equal bounds/coordinates for barrier-rule center controls.
    result['rule_controls'] = []
    for rule in (90,150,210):
        tr = center_trace(rule, 527)
        rc = rank_certificate(matrix(tr,5,0,5),5)
        result['rule_controls'].append({'rule':rule,'prefix':''.join(map(str,tr[:24])),**rc})
    # Strictly stronger target: on t<2^k, Thue-Morse differences are all one.
    tm = [i.bit_count()%2 for i in range(528)]
    result['thue_morse_control'] = rank_certificate(matrix(tm,5,0,5),5)
    assert result['thue_morse_control']['rank']==1
    result['status']='completed_exact_finite_computation'
    result['seconds']=time.monotonic()-START
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2),flush=True)

if __name__ == '__main__': main()
