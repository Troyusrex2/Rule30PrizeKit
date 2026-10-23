"""Independent cellwise checks for the forbidden-suffix certificates.

Enumerate every initial strip and every right-boundary history. This deliberately
does not implement Lean's packed strip update. These checks are supplementary;
the unbounded-prefix and unbounded-time claims are proved in Lean.
"""

from itertools import product
import json


def step(cells, left, right):
    return tuple(
        (left if j == 0 else cells[j - 1])
        ^ (cell | (right if j + 1 == len(cells) else cells[j + 1]))
        for j, cell in enumerate(cells)
    )


def successors(width, word):
    reached = set()
    trajectories = 0
    witness = None
    for initial in product((0, 1), repeat=width):
        for boundary in product((0, 1), repeat=len(word)):
            cells = initial
            for left, right in zip(map(int, word), boundary):
                cells = step(cells, left, right)
            reached.add(cells)
            trajectories += 1
            if not any(cells) and witness is None:
                witness = {"initial": initial, "right_boundary": boundary}
    return reached, trajectories, witness


def main():
    certificates = []
    for width, word in ((5, "011"), (6, "001001"), (6, "111001")):
        reached, count, witness = successors(width, word)
        assert witness is None, (width, word, witness)
        mask = sum(1 << sum(bit << j for j, bit in enumerate(row)) for row in reached)
        certificates.append({"width": width, "suffix": word,
                             "trajectories": count, "reachable_states": len(reached),
                             "reachable_mask": str(mask), "vacuum_absent": True})

    # Neither reducing the first width nor dropping its initial zero is valid.
    controls = []
    for width, word in ((4, "011"), (5, "11"), (5, "01"), (5, "")):
        _, count, witness = successors(width, word)
        assert witness is not None, (width, word)
        controls.append({"width": width, "suffix": word,
                         "trajectories": count, "vacuum_witness": witness})
    print(json.dumps({"passed": True, "certificates": certificates,
                      "negative_controls": controls,
                      "lean_kernel_verification": False}, indent=2))


if __name__ == "__main__":
    main()
