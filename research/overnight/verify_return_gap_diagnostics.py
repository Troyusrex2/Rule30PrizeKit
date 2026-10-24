"""Audit the return-sampled obstruction without an optimizer or array library."""

import argparse
from collections import Counter
import json
from pathlib import Path

from verify_gap_diagnostics import DIM, forward, vector


def verify(path):
    data = json.loads(path.read_text(encoding='utf-8'))
    assert not data['Lean_verified'] and not data['full_problem_solved']
    assert data['sampling']=='successive_common_rising_edges'
    assert data['transition_domain']=='seed' and data['features']==DIM
    assert data['dual']['exact_certificate_passed']
    gains, reward, seed = [0]*DIM, 0, [1]
    times, lags, durations = set(), set(), Counter()
    for term in data['dual']['terms']:
        a, b, c = int(term['outer']), int(term['inner']), term['center']
        d, weight = term['duration'], int(term['multiplier'])
        assert d>=2 and weight>0 and a&1 and b>0
        lag = (b & -b).bit_length()-1
        assert 2<=lag<c<b.bit_length()-1<a.bit_length()-1
        t = c-lag
        while len(seed)<=t+lag+d+1:
            seed.append(forward(seed[-1]))
        assert a==seed[t+lag] and b==seed[t] << lag
        states, heads = [], []
        x, y, center = a, b, c
        for tick in range(d+2):
            left, right = (x >> center) & 1, (y >> center) & 1
            assert left==right
            heads.append(left)
            states.append((x, y, center))
            assert x==seed[t+lag+tick] and y==seed[t+tick] << lag
            x, y, center = forward(x), forward(y), center+1
        assert [j for j in range(d+1) if heads[j:j+2]==[0, 1]]==[0, d]
        old, new = vector(a, b, c), vector(*states[d])
        for j in range(DIM):
            gains[j] += weight*(new[j]-old[j])
        reward += weight
        times.add(t)
        lags.add(lag)
        durations[d] += 1
    assert gains==list(map(int, data['dual']['gains']))
    assert min(gains)>=0 and reward==int(data['dual']['weighted_reward'])>0
    return {'AllPassed': True, 'Lean_verified': False, 'full_problem_solved': False,
        'optimizer_used': False, 'array_library_used': False,
        'forward_update': 'independent cellwise Rule 30',
        'features': 'scalar maxima with Kadane subarray scans',
        'certificate_terms': len(data['dual']['terms']), 'seed_time_range': [min(times), max(times)],
        'lags': sorted(lags), 'durations': dict(sorted(durations.items())),
        'all_ticks_agree': True, 'endpoints_are_successive_rising_edges': True,
        'minimum_gain': str(min(gains)), 'positive_weighted_reward': str(reward)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = verify(args.certificate)
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
