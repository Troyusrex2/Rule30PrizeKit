"""Independent finite controls for the controlled response/Q equivalence."""
from functools import lru_cache
import json
from pathlib import Path


def scalar_step(boundary, state, cells):
    # Direct use of rule 30, rather than the Q/prepend packed formula.
    value = 0
    for k in range(cells):
        left = boundary if k == 0 else (state >> (k-1)) & 1
        middle = (state >> k) & 1
        right = (state >> (k+1)) & 1
        value |= (left ^ (middle | right)) << k
    return value


def q_signature(state, horizon):
    value = 0
    for t in range(horizon):
        if t % 2 == 0:
            value |= (state & 1) << t
        else:
            value |= ((state | (state >> 1)) & 1) << t
            state ^= (state >> 1) | (state >> 2)
    return value


def main():
    intern = [{} for _ in range(21)]

    @lru_cache(None)
    def tree(horizon, state):
        state &= (1 << horizon)-1
        if horizon == 0:
            return 0
        key = (state & 1,
            tree(horizon-1, scalar_step(0, state, horizon-1)),
            tree(horizon-1, scalar_step(1, state, horizon-1)))
        if key not in intern[horizon]:
            intern[horizon][key] = len(intern[horizon])
        return intern[horizon][key]

    cases = []
    for width in range(1, 8):
        for horizon in range(1, 21):
            pairs = {(tree(horizon, r), q_signature(r, horizon)) for r in range(1 << width)}
            # The two independently calculated labels induce identical partitions.
            assert len(pairs) == len({a for a, _ in pairs}) == len({b for _, b in pairs})
            cases.append({'width': width, 'horizon': horizon, 'classes': len(pairs), 'pass': True})
    report = {'finite_controls_only': True, 'kernel_proof_replaced': False,
        'scalar_rule_table_implementation': True, 'cases': cases,
        'all_passed': all(c['pass'] for c in cases)}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'cases': len(cases), 'all_passed': report['all_passed'],
                      'cached_tree_nodes': tree.cache_info().currsize}))


if __name__ == '__main__':
    main()
