"""Test a structural route to the full problem, not additional tail exclusions.

Hypothesis under investigation: equal infinite center traces of finite nonzero
configurations force equal left-edge positions. Comparing a row with a later
row would then exclude every eventual period. Full trace injectivity is false
(the stripe examples already refute it). These computations are finite tests.
"""
import argparse
import json
from pathlib import Path
import time


def phi(row):
    return row ^ ((row << 1) | (row << 2))


def center_trace(row, width, length):
    trace = 0
    for t in range(length):
        trace |= ((row >> (width + t)) & 1) << t
        row = phi(row)
    return trace


def scan(width, length, extension):
    started = time.monotonic()
    groups = {}
    for row in range(1 << (2 * width + 1)):
        trace = center_trace(row, width, length)
        groups.setdefault(trace, []).append(row)
    collisions = [rows for rows in groups.values() if len(rows) > 1]
    mixed = [rows for rows in groups.values() if len({r.bit_length() for r in rows}) > 1]
    examples = []
    for rows in collisions[:12]:
        a, b = rows[:2]
        ta, tb = center_trace(a, width, extension), center_trace(b, width, extension)
        examples.append({"initial_rows": [a, b], "agree_through": length - 1,
                         "extended_length": extension, "extended_equal": ta == tb,
                         "first_difference": None if ta == tb else ((ta ^ tb) & -(ta ^ tb)).bit_length() - 1})
    result = {"width": width, "row_count": 1 << (2 * width + 1),
              "horizon": length, "collision_groups": len(collisions),
              "colliding_rows": sum(map(len, collisions)), "examples": examples,
              "mixed_left_edge_groups": len(mixed),
              "seconds": round(time.monotonic() - started, 3)}
    if not mixed:
        def ambiguous(horizon):
            mask = (1 << horizon) - 1
            labels = {}
            for trace, rows in groups.items():
                key, edge = trace & mask, rows[0].bit_length()
                if key in labels and labels[key][0] != edge:
                    return [labels[key][1], rows[0]]
                labels[key] = (edge, rows[0])
            return None
        low, high = 0, length
        while low < high:
            mid = (low + high) // 2
            if ambiguous(mid) is None:
                high = mid
            else:
                low = mid + 1
        result['minimum_edge_observation_length'] = low
        result['last_ambiguous_edge_pair'] = ambiguous(low - 1) if low else None
    if not collisions:
        traces = list(groups)
        low, high = 0, length
        while low < high:
            mid = (low + high) // 2
            mask = (1 << mid) - 1
            if len({trace & mask for trace in traces}) == len(traces):
                high = mid
            else:
                low = mid + 1
        result["minimum_injective_observation_length"] = low
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-width", type=int, default=7)
    parser.add_argument("--horizon", type=int, default=128)
    parser.add_argument("--extension", type=int, default=4096)
    args = parser.parse_args()
    results = []
    output = Path(__file__).parent / "trace-observability.json"
    for width in range(args.max_width + 1):
        result = scan(width, args.horizon, args.extension)
        results.append(result)
        output.write_text(json.dumps({"finite_experiment_only": True, "results": results}, indent=2) + "\n",
                          encoding="utf-8", newline="\n")
        print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
