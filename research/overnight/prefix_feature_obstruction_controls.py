"""Independent exact controls for the concrete Lean rank obstructions."""
import json
from pathlib import Path

from stripe_prefix_dfa_potential import Model, add, scalar_z


def list_z(a):
    bits = [0]+[(a >> j) & 1 for j in range(a.bit_length())]+[0, 0]
    out = [bits[k+1] ^ (bits[k] | bits[k-1]) for k in range(1, len(bits)-1)]
    return sum(bit << j for j, bit in enumerate(out))


def main():
    witnesses = [(323, 3), (1277, 8), (1341, 6), (1917, 7), (2371, 38),
                 (2429, 13), (2653, 5), (4035, 2), (4093, 4)]
    report = {'independent_exact_controls_only': True, 'Lean_proof_in_separate_module':
        'Rule30PrefixRankObstructionResearch', 'prize_problem_proved': False,
        'single_transition_feature_equalities': [], 'free_flip_balances': []}
    for r, parity, a in [(2, False, 203), (2, True, 203), (4, False, 143659)]:
        m = Model(r, parity)
        b = scalar_z(scalar_z(a))
        assert list_z(list_z(a)) == b
        assert m.final_mode(a) == m.final_mode(b) == 2
        assert m.features(a) == m.features(b)
        report['single_transition_feature_equalities'].append({'radius': r, 'ones_parity': parity,
            'old': a, 'new': b, 'equal': True})
    for parity in [False, True]:
        m = Model(2, parity)
        balance = {}
        rows = []
        reward = 0
        for a, multiplicity in witnesses:
            b = scalar_z(scalar_z(a))
            assert list_z(list_z(a)) == b
            assert m.final_mode(a) == m.final_mode(b) == 2
            assert (a >> 1) & 1 != (b >> 1) & 1
            for j, value in m.features(b).items(): add(balance, j, multiplicity*value)
            for j, value in m.features(a).items(): add(balance, j, -multiplicity*value)
            reward += multiplicity
            rows.append({'old': a, 'new': b, 'multiplicity': multiplicity})
        assert not balance and reward == 86
        report['free_flip_balances'].append({'radius': 2, 'ones_parity': parity,
            'rows': rows, 'exact_weighted_feature_gain_zero': True, 'total_flip_charge': reward})
    output = Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'single_transition_controls': 3, 'weighted_balances': 2,
                      'independent_list_updates_checked': 21, 'passed': True}))


if __name__ == '__main__':
    main()
