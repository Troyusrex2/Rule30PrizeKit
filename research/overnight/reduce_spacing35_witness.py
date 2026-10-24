"""Find a small periodic gate with a reconstructed white run of length 17."""
import importlib.util
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('probe', HERE / 'spacing35_row_probe.py')
probe = importlib.util.module_from_spec(sp)
sp.loader.exec_module(probe)


def witness(gaps, depth=1024):
    row = probe.initial_row(gaps, depth)
    bits = ''.join(str((row >> k) & 1) for k in range(depth))
    start = bits.find('0' * 17)
    if start < 0:
        return None
    probe.check_forward(gaps, row, depth)
    return {'periodic_gate_gaps': list(gaps), 'gate_period': sum(gaps),
            'first_white_depth': start + 1, 'white_run_length': 17,
            'initial_prefix': bits[:start + 18], 'forward_checked': True,
            'finite_observations_only': True, 'right_realizability_claim': False}


def main():
    target = HERE / 'spacing35-small-witness.json'
    best = None
    for length in range(1, 11):
        for gaps in itertools.product([3, 5], repeat=length):
            result = witness(gaps)
            if result is not None and (best is None or
                    (result['gate_period'], result['first_white_depth']) <
                    (best['gate_period'], best['first_white_depth'])):
                best = result
                target.write_text(json.dumps(best, indent=2) + '\n', encoding='utf-8', newline='\n')
                print(json.dumps({k:v for k,v in best.items() if k != 'initial_prefix'}), flush=True)
    print(json.dumps({'completed': True, 'found': best is not None}))


if __name__ == '__main__':
    main()
