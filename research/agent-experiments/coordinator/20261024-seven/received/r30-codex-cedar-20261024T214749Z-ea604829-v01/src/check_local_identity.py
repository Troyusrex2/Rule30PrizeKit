"""Exhaustive local control only; no nonperiodicity or Lean proof claim."""
import itertools
import json
import platform
from datetime import datetime, timezone

# Indexed by 4*left + 2*center + right, from 000 through 111.
RULE30 = (0, 1, 1, 1, 1, 0, 0, 0)

def table_rule(left, center, right):
    return RULE30[4*left + 2*center + right]

def main():
    rule_cases = []
    for left, center, right in itertools.product((0, 1), repeat=3):
        expected = table_rule(left, center, right)
        computed = left ^ (center | right)
        if expected != computed:
            raise AssertionError((left, center, right, expected, computed))
        rule_cases.append({"input": [left, center, right], "output": expected})
    cases = []
    for al, ac, ar, bl, bc, br in itertools.product((0, 1), repeat=6):
        dl, dc, dr = al ^ bl, ac ^ bc, ar ^ br
        actual = table_rule(al, ac, ar) ^ table_rule(bl, bc, br)
        graph = dl ^ ((1 ^ ar) & dc) ^ ((1 ^ bc) & dr)
        if actual != graph:
            raise AssertionError((al, ac, ar, bl, bc, br, actual, graph))
        cases.append({"a": [al, ac, ar], "b": [bl, bc, br],
                      "actual_difference": actual, "path_recurrence": graph})
    result = {
        "status": "PASS",
        "checked_utc": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "python": platform.python_version(),
        "rule_table_cases": len(rule_cases),
        "paired_neighborhood_cases": len(cases),
        "scope": "Exhaustive local identity only. No graph pairing, global progress, infinite trace, Lean or Wolfram verification.",
        "rule_table": rule_cases,
        "paired_cases": cases,
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
