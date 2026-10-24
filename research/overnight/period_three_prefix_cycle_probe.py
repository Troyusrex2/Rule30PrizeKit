"""An exact finite collision of the proposed prefix-only score signatures.

This rejects those prefix-only candidate features; it is not a counterexample
to the period-three conjecture. No Lean verification is claimed by the probe.
"""
import json
from pathlib import Path

from period_three_ribbon_rank_probe import Model,G,good,scalar_cycle,BASE
from period_three_ribbon_graph import admissible


def main():
    words = [3680,25783,227424,1640567]
    for a,b in zip(words,words[1:]):
        assert G(a) == b == scalar_cycle(a,a.bit_length())
    assert all(good(a) and admissible(a) for a in words)
    defects = [next(k for k in range(a.bit_length()+12)
                    if ((a >> k) & 1) != BASE[a & 1][k % 12]) for a in words]
    assert defects == [3,3,3,3]
    model = Model(2)
    def signature(a,b):
        return {j:v for j,v in model.features(a,b).items()
                if j >= model.dim-4 or (j // model.patterns) % 4 != 0}
    first = signature(words[1],words[0])
    last = signature(words[3],words[2])
    assert first == last
    assert [(a & 1) for a in words] == [0,1,0,1]
    report = {'Lean_verified':False,'full_problem_claim':False,'C3w_011_proved':False,
              'AllExactFiniteControlsPassed':True,'words':words,'first_defects':defects,
              'packed_and_scalar_G_agree':True,'head_bits':[0,1,0,1],
              'two_step_prefix_score_signatures_equal':True,'charged_head_flips':2,
              'prefix_signature':{str(j):v for j,v in first.items()},
              'arbitrary_score_or_rank_refuted':False}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report),flush=True)


if __name__ == '__main__':
    main()
