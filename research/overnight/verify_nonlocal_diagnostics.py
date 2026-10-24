"""Recompute exact discovery certificates without invoking an optimizer.

These are mathematical diagnostics, not Lean-verified statements. They only
reject the explicitly specified finite feature cones. No prize claim follows.
"""

import json
from pathlib import Path

import numpy as np

import paired_nonlocal_rank_probe as pair
from paired_prefix_sos_probe import analyze_dual, grams


HERE = Path(__file__).resolve().parent


def read(name):
    return json.loads((HERE/name).read_text(encoding='utf-8'))


def records(chosen):
    result = []
    for item in chosen:
        a, b, c = int(item['outer']), int(item['inner']), item['center_index']
        assert pair.nested(a, b, c)
        na, nb = pair.step(a), pair.step(b)
        old_mode, new_mode = (a >> c) & 1, (na >> (c+1)) & 1
        assert old_mode == (b >> c) & 1 and new_mode == (nb >> (c+1)) & 1
        reward = int(old_mode != new_mode)
        assert reward == item['reward'] and item['multiplier'] > 0
        result.append((a, b, c, pair.features(a, b, c),
                       pair.features(na, nb, c+1), reward))
    return result


def audit_gram_certificate(certificate, color=False, seed_lag=None, restart_lag=None):
    rs = records(certificate['chosen'])
    count = 2 if color else 1
    linear = np.zeros((len(rs), 252*count), dtype=object)
    delta = np.zeros((len(rs), 5*count, 4, 4), dtype=object)
    seed = [1]
    if seed_lag is not None:
        for _ in range(max(r[2] for r in rs)+1):
            seed.append(pair.step(seed[-1]))
    for i, (a, b, c, old, new, _) in enumerate(rs):
        if restart_lag is not None:
            assert b % (1 << restart_lag) == 0
            outer = b >> restart_lag
            for _ in range(restart_lag):
                outer = pair.step(outer)
            assert outer == a
        if seed_lag is not None:
            t = c-seed_lag
            assert t >= 1 and a == seed[t+seed_lag] and b == seed[t] << seed_lag
        for updated, sign in ((False, -1), (True, 1)):
            aa, bb, cc, values = (pair.step(a), pair.step(b), c+1, new) if updated else (a, b, c, old)
            mode = ((aa >> cc) & 1) if color else 0
            linear[i, 252*mode:252*(mode+1)] += sign*values[:252].astype(object)
            delta[i, 5*mode:5*(mode+1)] += sign*grams(aa, bb, cc).astype(object)
    result = analyze_dual(rs, linear, delta, [r[5] for r in rs],
                          [s['multiplier'] for s in certificate['chosen']])
    assert result['passed']
    for key in ['combined_reward', 'linear_gain_min', 'principal_minors', 'gram_gains', 'chosen']:
        assert result[key] == certificate[key], key
    return {'chosen_cases': len(rs), 'gram_blocks': 5*count,
            'combined_reward': result['combined_reward'],
            'minimum_linear_gain': result['linear_gain_min'], 'exact_arithmetic_passed': True,
            'actual_seed_lag': seed_lag, 'exact_restart_lag': restart_lag}


def main():
    finite = read('paired-nonlocal-rank-dual.json')
    rs = records(finite['chosen'])
    gains = sum((s['multiplier']*(r[4]-r[3]).astype(object)
                 for s, r in zip(finite['chosen'], rs)), np.zeros(pair.DIM, dtype=object))
    reward = sum(s['multiplier']*r[5] for s, r in zip(finite['chosen'], rs))
    assert list(gains) == finite['combined_feature_gains']
    assert min(gains) >= 0 and reward == finite['combined_reward'] > 0
    generic = read('restart-prefix-sdp-lag2-cegar.json')['iterations'][-1]['rational_dual_attempt']
    actual_seed = read('seed-nonlocal-sdp-color-lag2-refined.json')['results'][-1]['rational_dual_attempt']
    report = {'Lean_verified': False, 'full_problem_solved': False,
              'scope': 'Exact diagnostic rejection of specified feature cones only',
              'paired_292_features': {'chosen_cases': len(rs), 'combined_reward': reward,
                                      'exact_arithmetic_passed': True},
              'restart_5_gram': audit_gram_certificate(generic, restart_lag=2),
              'seed_10_gram': audit_gram_certificate(actual_seed, color=True, seed_lag=2),
              'AllPassed': True}
    (HERE/'nonlocal-diagnostics-check.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
