"""Probe finite stripe extensions followed by finite inverse steps.

Only finite evidence is reported. The experiment does not assert that all
trace-equivalent configurations arise through this construction.
"""
import argparse
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('caps', HERE/'finite-preimage-caps.py')
caps = importlib.util.module_from_spec(spec)
spec.loader.exec_module(caps)


def search(max_source=255, max_depth=7, max_cap=24):
    checked = accepted = changed = 0
    examples = []
    for source in range(1, max_source+1):
        anchor = (source & -source).bit_length()-1
        image = source
        for depth in range(1, max_depth+1):
            image = caps.phi(image)
            shifted = image >> anchor
            # The stripe identity requires a black anchor with a white cell
            # immediately to its left. Skip any other local pattern.
            if depth < anchor or (shifted & 3) != 1:
                continue
            stripe = 1
            for cap in range(max_cap+1):
                if cap:
                    stripe = 2*stripe+(1 if cap % 2 else -1)
                center = cap-anchor
                checked += 1
                row = (shifted << cap) | (stripe ^ (1 << cap))
                for _ in range(depth):
                    row = caps.finite_inverse(row)
                    if row is None:
                        break
                if row is None or caps.trace(row, center, depth) != caps.trace(source, 0, depth):
                    continue
                accepted += 1
                # A separate executed check of the observed trace agreement.
                assert caps.trace(row, center, depth+128) == caps.trace(source, 0, depth+128)
                prefix = row >> center if center >= 0 else row << (-center)
                if prefix != source:
                    changed += 1
                    if len(examples) < 12:
                        examples.append({'source': source, 'inverse_depth': depth,
                                         'cap_length': cap, 'row': row, 'center_index': center})
    return {'finite_construction_search_only': True, 'sources': [1, max_source],
            'inverse_depths': [1, max_depth], 'cap_lengths': [0, max_cap],
            'constructions_checked': checked, 'accepted': accepted,
            'changed_left_prefix_count': changed, 'examples': examples}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-source', type=int, default=255)
    parser.add_argument('--max-depth', type=int, default=7)
    parser.add_argument('--max-cap', type=int, default=24)
    args = parser.parse_args()
    report = search(args.max_source, args.max_depth, args.max_cap)
    (HERE/'finite-alias-construction-search.json').write_text(
        json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
