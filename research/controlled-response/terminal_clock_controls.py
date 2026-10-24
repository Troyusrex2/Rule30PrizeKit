"""Independent finite controls for the all-clock Lean correspondence.

Scalar integer Q evolution is compared directly on both sides, including
equality of orbit points. This calculation is not the unbounded proof.
"""
import json
from pathlib import Path
import random
import time


def q(x):
    return x ^ ((x >> 1) | (x >> 2))


def case(n, prefix, a, horizon):
    short = prefix | ((a | 2) << n)
    long = prefix | ((a | ((1-a) << 1) | 4) << n)
    initial_short, initial_long = short, long
    forward, backward = {}, {}
    returns = 0
    for t in range(horizon+1):
        bit = (short >> n) & 1
        expanded = (short & ((1 << n)-1)) | ((bit | ((1-bit) << 1) | 4) << n)
        bit_long = (long >> n) & 1
        reduced = (long & ((1 << n)-1)) | ((bit_long | 2) << n)
        assert expanded == long and reduced == short
        assert (long & 1) == (short & 1)
        assert ((long | (long >> 1)) & 1) == ((short | (short >> 1)) & 1)
        assert forward.setdefault(short, long) == long
        assert backward.setdefault(long, short) == short
        assert (short == initial_short) == (long == initial_long)
        returns += short == initial_short
        short, long = q(short), q(long)
    return returns


def main():
    started = time.monotonic()
    cases = checks = returns = 0
    for n in range(12):
        for prefix in range(1 << n):
            for a in (0, 1):
                returns += case(n, prefix, a, 128)
                cases += 1
                checks += 129
    rng = random.Random(202610240731)
    wide = []
    for i in range(256):
        n = rng.randrange(12, 257)
        prefix = rng.getrandbits(n)
        a = rng.randrange(2)
        returns += case(n, prefix, a, 256)
        cases += 1
        checks += 257
        if len(wide) < 8:
            wide.append([n, prefix, a])
    report = {'FiniteControlsOnly': True, 'LeanVerifiedByThisCalculation': False,
              'FullProblemClaim': False, 'Cases': cases, 'WideCases': 256,
              'ExhaustivePrefixLengths': list(range(12)), 'MaximumPrefixLength': 256,
              'StatePairsChecked': checks, 'DetectedReturnTimesIncludingZero': returns,
              'AllPassed': True, 'Seconds': round(time.monotonic()-started, 3),
              'WolframSamples': [[n, str(prefix), a] for n, prefix, a in wide]}
    here = Path(__file__).resolve().parent
    here.joinpath('terminal_clock_controls.json').write_text(
        json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'WolframSamples'}), flush=True)


if __name__ == '__main__':
    main()
