"""Cellwise, exhaustive checks independent of the generator's packed updater."""
from functools import lru_cache
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def cellwise(width, left, right, row):
    cells = tuple((row >> j) & 1 for j in range(width))
    return sum(((left if j == 0 else cells[j-1]) ^
                (cells[j] | (right if j+1 == width else cells[j+1]))) << j
               for j in range(width))


@lru_cache(None)
def table(width, driver):
    return tuple((cellwise(width, driver, 0, row), cellwise(width, driver, 1, row))
                 for row in range(1 << width))


def predecessor(width, driver, target):
    return {row for row, successors in enumerate(table(width, driver))
            if any(successor in target for successor in successors)}


def reverse_word(width, word):
    states = {0}
    for bit in reversed(word):
        states = predecessor(width, int(bit), states)
    return states


def main():
    records = json.loads((ROOT / "research/six-tail/certificates.json").read_text(encoding="utf-8"))
    checked, edges = [], 0
    for record in records:
        word, width, padding = record["word"], record["width"], record["white_steps"]
        driver = "0" * padding + word
        states = [set(row) for row in record["predecessor_sets"]]
        assert len(states) == len(driver)+1 and not states[0] and states[-1] == {0}
        for phase, bit in enumerate(driver):
            assert predecessor(width, int(bit), states[phase+1]) == states[phase], (word, phase)
            edges += 2 * (1 << width)
        checked.append({"word": word, "width": width, "white_steps": padding,
                        "predecessor_steps": len(driver), "passed": True})
    # These finite strip obstructions fail when the necessary width/padding is removed.
    controls = []
    for width, padding, word in ((14, 13, "110001"), (13, 14, "110001"), (14, 14, "10101")):
        states = reverse_word(width, "0" * padding + word)
        assert states, (width, padding, word)
        controls.append({"width": width, "white_steps": padding, "word": word,
                         "vacuum_predecessor_count": len(states), "example_initial_strip": min(states)})
    print(json.dumps({"passed": True, "certificates": checked, "edge_cases_checked": edges,
                      "negative_controls": controls, "lean_kernel_verification": False}, indent=2))


if __name__ == "__main__":
    main()
