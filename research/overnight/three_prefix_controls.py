"""Finite scalar controls for the necessary period-three first-defect rule."""
import json
from pathlib import Path
import random

from period_three_prefix_rank_probe import BASE, step


def check(word, mode):
    d = next(k for k in range(word.bit_length()+12)
             if ((word >> k) & 1) != BASE[mode][k % 12])
    value = word
    reference_head = ((0, 0, 1), (1, 0, 1))[mode]
    for t in range(d):
        assert (value & 1) == reference_head[t % 3]
        value = step(value, int(t % 3 == 1))
    assert (value & 1) != reference_head[d % 3]
    if d % 3 != 0:
        assert (value & 1) != int(d % 3 == 2)
    return d


def main():
    cases = fixed_phase = maximum = 0
    for word in range(1 << 14):
        d = check(word, word & 1)
        cases += 1
        fixed_phase += int(d % 3 != 0)
        maximum = max(maximum, d)
    rng = random.Random(202610240800)
    samples = []
    for _ in range(256):
        mode = rng.randrange(2)
        d = rng.randrange(3, 401)
        prefix = sum(BASE[mode][k % 12] << k for k in range(d))
        word = prefix | ((1-BASE[mode][d % 12]) << d)
        word |= rng.getrandbits(rng.randrange(1, 80)) << (d+1)
        assert check(word, mode) == d
        maximum = max(maximum, d)
        fixed_phase += int(d % 3 != 0)
        cases += 1
        if len(samples) < 8 and d < 90:
            samples.append([str(word), mode, d])
    report = {'FiniteControlsOnly': True, 'LeanVerifiedByThisCalculation': False,
              'FullProblemClaim': False, 'AllPassed': True, 'Cases': cases,
              'AllWordsBelow': 1 << 14, 'WideControlledFirstDefects': 256,
              'FixedPhaseViolationsDetected': fixed_phase, 'MaximumFirstDefect': maximum,
              'ReferenceCodes': [sum(v << k for k, v in enumerate(b)) for b in BASE],
              'WolframSamples': samples}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n',
                                                 encoding='utf-8', newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'WolframSamples'}), flush=True)


if __name__ == '__main__':
    main()
