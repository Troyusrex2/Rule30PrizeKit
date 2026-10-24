"""Recheck saved gap-score obstructions using integers and no optimizer.

The forward update is cellwise. Feature maxima use scalar scans, including
Kadane's recurrence for the subarray maximum. This is an arithmetic audit,
not Lean kernel verification or a solution of a prize problem.
"""

import argparse
from itertools import product
import json
from pathlib import Path


CHARGES = [v for v in product((-1, 0, 1), repeat=4) if max(v)>0]
BASE_DIM = 6*len(CHARGES)+1
DIM = 2*BASE_DIM


def forward(row):
    cells = [0, 0]+[(row >> i) & 1 for i in range(row.bit_length())]+[0, 0]
    out = 0
    for i in range(row.bit_length()+2):
        out |= (cells[i] ^ (cells[i+1] | cells[i+2])) << i
    return out


def vector(a, b, center):
    values = []
    for indices in (range(center), range(center+1, a.bit_length())):
        word = [((a >> j) & 1)+2*((b >> j) & 1) for j in indices]
        prefix, suffix, subarray = [], [], []
        for charge in CHARGES:
            total = best = 0
            for symbol in word:
                total += charge[symbol]
                best = max(best, total)
            prefix.append(best)
            total = best = 0
            for symbol in reversed(word):
                total += charge[symbol]
                best = max(best, total)
            suffix.append(best)
            ending = best = 0
            for symbol in word:
                ending = max(0, ending+charge[symbol])
                best = max(best, ending)
            subarray.append(best)
        values.extend(prefix+suffix+subarray)
    values.append(1)
    result = [0]*DIM
    start = ((a >> center) & 1)*BASE_DIM
    result[start:start+BASE_DIM] = values
    assert len(result)==DIM and min(result)>=0
    return result


def verify(path):
    data = json.loads(path.read_text(encoding='utf-8'))
    assert not data['Lean_verified'] and not data['full_problem_solved']
    assert data['features']==DIM and data['dual']['exact_certificate_passed']
    domain = data.get('transition_domain', 'nested')
    assert domain in ('nested', 'restart', 'seed')
    gains, reward, seed_rows, lags, times = [0]*DIM, 0, [1], set(), set()
    for term in data['dual']['terms']:
        a, b, c, weight = int(term['outer']), int(term['inner']), term['center'], int(term['multiplier'])
        assert a>0 and b>0 and a&1 and weight>=0
        low = (b & -b).bit_length()-1
        assert 0 < low < c < b.bit_length()-1 < a.bit_length()-1
        assert (a >> c) & 1 == (b >> c) & 1
        na, nb = forward(a), forward(b)
        assert (na >> (c+1)) & 1 == (nb >> (c+1)) & 1
        if domain in ('restart', 'seed'):
            assert low>=2
            original = b >> low
            outer = original
            for _ in range(low):
                outer = forward(outer)
            assert outer==a
            lags.add(low)
            if domain=='seed':
                time = c-low
                assert time>=1
                while len(seed_rows)<=time+low:
                    seed_rows.append(forward(seed_rows[-1]))
                assert original==seed_rows[time] and a==seed_rows[time+low]
                times.add(time)
        old, new = vector(a, b, c), vector(na, nb, c+1)
        for j in range(DIM):
            gains[j] += weight*(new[j]-old[j])
        reward += weight*int(((a >> c) & 1) != ((na >> (c+1)) & 1))
    assert gains==list(map(int, data['dual']['gains']))
    assert min(gains)>=0 and reward==int(data['dual']['weighted_reward'])>0
    return {'file': path.name, 'transition_domain': domain, 'features': DIM,
            'certificate_terms': len(data['dual']['terms']), 'AllPassed': True,
            'minimum_gain': str(min(gains)), 'positive_weighted_reward': str(reward),
            'lags': sorted(lags), 'seed_time_range': [min(times), max(times)] if times else None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--files', nargs='+', type=Path, default=[Path(__file__).with_name(n)
        for n in ('paired-gap-rank-probe.json', 'restart-gap-rank-probe.json', 'seed-gap-rank-probe.json')])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    results = [verify(p) for p in args.files]
    report = {'AllPassed': True, 'Lean_verified': False, 'full_problem_solved': False,
              'optimizer_used': False, 'forward_update': 'independent cellwise Rule 30',
              'features': 'independent scalar maxima with Kadane subarray scans', 'results': results}
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
