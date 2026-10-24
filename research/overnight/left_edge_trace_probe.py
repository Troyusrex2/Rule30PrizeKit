"""Falsify finite-row left-edge observability; finite agreement is not a proof.

Bit k of a is initially at physical position center_index-k.  The full
Rule-30 moving-frame update is a ^ ((a << 1) | (a << 2)); at time t the
physical center is at bit center_index+t.  The leading set bit therefore
determines the left edge.  No real machine configuration or key is read.
"""

import argparse
import json
from pathlib import Path
from time import perf_counter


def step(a):
    return a ^ ((a << 1) | (a << 2))


def signature(a, center_index, count):
    result = 0
    for t in range(count):
        result |= ((a >> (center_index + t)) & 1) << t
        a = step(a)
    return result


def scalar_trace(a, center_index, count):
    row = {center_index-k for k in range(a.bit_length()) if (a >> k) & 1}
    out = []
    for _ in range(count):
        out.append(int(0 in row))
        if row:
            row = {p for p in range(min(row)-1, max(row)+2)
                   if ((p-1 in row) ^ ((p in row) or (p+1 in row)))}
    return sum(x << t for t, x in enumerate(out))


def run(width, center_index, count, extension):
    started = perf_counter()
    controls = [0, 1, 2, 3, 55, 56, 1272, 3680, (1 << width)-1]
    assert all(signature(a, center_index, 40) == scalar_trace(a, center_index, 40)
               for a in controls)
    # Retain one representative of each left edge in every signature class.
    groups = {}
    collisions = []
    for a in range(1, 1 << width):
        s = signature(a, center_index, count)
        edge = a.bit_length()
        representatives = groups.setdefault(s, {})
        if representatives and edge not in representatives:
            collisions.append([next(iter(representatives.values())), a])
        representatives.setdefault(edge, a)
    extended = []
    for a, b in collisions:
        sa = signature(a, center_index, extension)
        sb = signature(b, center_index, extension)
        first_difference = (sa ^ sb)
        extended.append({"a": a, "b": b,
                         "first_difference": ((first_difference & -first_difference).bit_length()-1
                                              if first_difference else None)})
    return {"claim": "Finite-prefix falsification probe only",
            "Lean_verified": False, "full_problem_solved": False,
            "width": width, "center_index": center_index,
            "initial_steps": count, "extension_steps": extension,
            "scalar_controls": len(controls), "tested_nonzero_rows": (1 << width)-1,
            "signature_classes": len(groups), "cross_left_edge_collisions": len(collisions),
            "extended_pairs": extended, "seconds": perf_counter()-started}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--width", type=int, default=16)
    parser.add_argument("--center-index", type=int, default=8)
    parser.add_argument("--steps", type=int, default=128)
    parser.add_argument("--extension", type=int, default=4096)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = run(args.width, args.center_index, args.steps, args.extension)
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if k != "extended_pairs"}))
    print(json.dumps(report["extended_pairs"][:20]))
