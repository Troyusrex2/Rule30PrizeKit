"""Falsify nonlocal natural-valued FlipRanking candidates for the full problem.

Pairs have strictly nested support EDGES; cellwise set containment is neither
assumed nor substituted. Both current and next center colors must agree.
The features count ordered pairs at arbitrary distances and prefix-count
squares, unlike the previous local position-weighted pattern model.

Finite fits are never proofs. No result here is used as a Lean premise.
"""

import argparse
import json
from pathlib import Path
import random
from time import perf_counter

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, vstack


REGION_PAIRS = [(0, 0), (0, 1), (0, 2), (1, 2), (2, 2)]
PAIR_INDEX = {pair: i for i, pair in enumerate(REGION_PAIRS)}
CHARGES = [(0, 1, -1, 0), (-1, 0, 0, 1), (0, 1, 1, -1), (-1, 1, 1, 0),
           (0, 1, 0, -1), (0, 0, 1, -1), (-1, 1, 0, 0), (-1, 0, 1, 0)]
DIM = 12+5*3*16+2*2*len(CHARGES)+len(CHARGES)


def step(a):
    # Bit k is at physical position lo+k. The next left edge is lo-1.
    return (a << 2) ^ ((a << 1) | a)


def nested(a, b, center):
    if not a or not b or not (a & 1):
        return False
    low_b = (b & -b).bit_length()-1
    high_b = b.bit_length()-1
    return 0 < low_b < center < high_b < a.bit_length()-1


def letters(a, b, center):
    return [(i-center, ((a >> i) & 1)+2*((b >> i) & 1))
            for i in range(a.bit_length())]


def region(p):
    return 0 if p < 0 else 1 if p == 0 else 2


def features(a, b, center, brute=False):
    cells = letters(a, b, center)
    out = np.zeros(DIM, dtype=np.int64)
    by_region = [[], [], []]
    for p, symbol in cells:
        r = region(p)
        out[r*4+symbol] += 1
        by_region[r].append(symbol)
    if brute:
        for j, (q, second) in enumerate(cells):
            for p, first in cells[:j]:
                rp = PAIR_INDEX[(region(p), region(q))]
                for degree in range(3):
                    out[12+(rp*3+degree)*16+4*first+second] += (q-p)**degree
    else:
        # Exact first/second position moments account for every distant pair.
        moments = [[[0, 0, 0] for _ in range(4)] for _ in range(3)]
        for p, second in cells:
            r = region(p)
            for before in range(r+1):
                if (before, r) not in PAIR_INDEX:
                    continue
                rp = PAIR_INDEX[(before, r)]
                for first in range(4):
                    count, linear, square = moments[before][first]
                    values = (count, p*count-linear, p*p*count-2*p*linear+square)
                    for degree, value in enumerate(values):
                        out[12+(rp*3+degree)*16+4*first+second] += value
            entry = moments[r][second]
            entry[0] += 1
            entry[1] += p
            entry[2] += p*p
    index = 252
    for side in (0, 2):
        for reverse in (False, True):
            word = by_region[side][::-1] if reverse else by_region[side]
            for charge in CHARGES:
                value = score = 0
                for symbol in word:
                    value += charge[symbol]
                    score += value*value
                out[index] = score
                index += 1
    for charge in CHARGES:
        total = sum(charge[symbol] for _, symbol in cells)
        out[index] = total*total
        index += 1
    assert index == DIM and out.min() >= 0
    return out


def controls():
    rng = random.Random(202610240912)
    scalar = pair_counts = 0
    for _ in range(256):
        width = rng.randrange(5, 40)
        center = rng.randrange(2, width-2)
        a = rng.getrandbits(width) | 1 | (1 << (width-1))
        b = rng.getrandbits(width-2) << 1
        b |= 1 << (center-1) | 1 << (center+1)
        assert nested(a, b, center)
        x = {i-center for i in range(width) if a >> i & 1}
        y = {i-center for i in range(width) if b >> i & 1}
        nx = {p for p in range(-center-1, width-center+1)
              if ((p-1 in x) ^ ((p in x) or (p+1 in x)))}
        ny = {p for p in range(-center-1, width-center+1)
              if ((p-1 in y) ^ ((p in y) or (p+1 in y)))}
        ax = sum(1 << (p+center+1) for p in nx)
        by = sum(1 << (p+center+1) for p in ny)
        assert ax == step(a) and by == step(b)
        assert nested(ax, by, center+1)
        scalar += 1
        assert np.array_equal(features(a, b, center), features(a, b, center, brute=True))
        assert np.array_equal(features(ax, by, center+1), features(ax, by, center+1, brute=True))
        pair_counts += 2
    return {'scalar_product_evolutions': scalar, 'moment_vs_brute_pair_counts': pair_counts,
            'nested_edges_preserved': True, 'AllPassed': True}


def cases(width):
    for center in range(2, width-2):
        for middle in range(1 << (width-2)):
            a = (middle << 1) | 1 | (1 << (width-1))
            na = step(a)
            for inside in range(1 << (width-2)):
                b = inside << 1
                if not nested(a, b, center) or (a >> center) & 1 != (b >> center) & 1:
                    continue
                nb = step(b)
                if (na >> (center+1)) & 1 != (nb >> (center+1)) & 1:
                    continue
                old = features(a, b, center)
                new = features(na, nb, center+1)
                reward = int(((a >> center) & 1) != ((na >> (center+1)) & 1))
                yield a, b, center, old, new, reward


def holdout(coefficients):
    rng = random.Random(202610240913)
    accepted = failures = 0
    worst = None
    for _ in range(50000):
        width = rng.randrange(5, 81)
        center = rng.randrange(2, width-2)
        a = rng.getrandbits(width) | 1 | (1 << (width-1))
        b = rng.getrandbits(width-2) << 1
        if not nested(a, b, center) or (a >> center) & 1 != (b >> center) & 1:
            continue
        na, nb = step(a), step(b)
        if (na >> (center+1)) & 1 != (nb >> (center+1)) & 1:
            continue
        old = features(a, b, center)
        new = features(na, nb, center+1)
        reward = int(((a >> center) & 1) != ((na >> (center+1)) & 1))
        residual = float((new-old) @ coefficients+reward)
        accepted += 1
        if residual > 1e-7:
            failures += 1
            if worst is None or residual > worst['residual']:
                worst = {'outer': str(a), 'inner': str(b), 'center_index': center,
                         'width': width, 'residual': residual, 'reward': reward}
        if accepted == 2048:
            break
    assert accepted == 2048
    return {'actual_nested_transitions': accepted, 'failures': failures, 'worst': worst}


def run(max_width, seconds, signed, output):
    began = perf_counter()
    report = {'Lean_verified': False, 'full_problem_solved': False,
              'FlipRanking_proved': False, 'potential_is_nonlocal': True,
              'features': DIM, 'signed_sample_lower_bound_only': signed,
              'controls': controls(), 'results': []}
    rows, rhs = [], []
    totals = 0
    for width in range(5, max_width+1):
        count = flips = 0
        for a, b, center, old, new, reward in cases(width):
            rows.append(new-old)
            rhs.append(-reward)
            if signed:
                rows.extend((-old, -new))
                rhs.extend((0, 0))
            count += 1
            flips += reward
        totals += count
        matrix = csr_matrix(np.array(rows, dtype=float))
        bound = np.array(rhs, dtype=float)
        objective = np.ones(DIM) if not signed else np.zeros(DIM)
        result = linprog(objective, A_ub=matrix, b_ub=bound,
                         bounds=[(None, None) if signed else (0, None)]*DIM,
                         method='highs', options={'time_limit': seconds})
        item = {'width': width, 'new_pairs': count, 'new_flips': flips,
                'total_pairs': totals, 'constraints': len(rhs), 'status': int(result.status),
                'message': result.message, 'candidate_accepted': False}
        if result.success:
            item['coefficients'] = result.x.tolist()
            item['max_training_residual'] = float(np.max(matrix @ result.x-bound))
            item['holdout'] = holdout(result.x)
        report['results'].append(item)
        report['seconds'] = perf_counter()-began
        output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
        print(json.dumps({k: v for k, v in item.items() if k != 'coefficients'}), flush=True)
        if not result.success:
            break
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-width', type=int, default=8)
    parser.add_argument('--seconds', type=int, default=20)
    parser.add_argument('--signed', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run(args.max_width, args.seconds, args.signed, args.output)
