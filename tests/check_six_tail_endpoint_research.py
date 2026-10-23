"""Independent exhaustive checks for the two endpoint refinements."""
import json
from pathlib import Path
from check_six_tail_backward_research import predecessor, table

ROOT = Path(__file__).resolve().parents[1]


def image(width, driver, states):
    transitions = table(width, driver)
    return {target for state in states for target in transitions[state]}


def forces(states, bit):
    return all(bool(state & 1) == bit for state in states)


def main():
    records = json.loads((ROOT / "research/six-tail/endpoint-certificates.json").read_text())
    results = []
    for r in records:
        width, word = r["width"], r["word"]
        z = set(r["Z"])
        p, s, q = ([set(row) for row in r[name]] for name in ("P", "S", "Q"))
        assert 0 in z and image(width, 0, z) == z
        assert s[0] == z and p[-1] == {0} and q[0] == p[0] and q[-1] == {0}
        for j, bit in enumerate(word):
            assert p[j] == predecessor(width, int(bit), p[j+1])
            assert s[j+1] == image(width, int(bit), s[j])
            if bit == "0":
                assert forces(s[j] & p[j], r["c"][j])
        for j in range(r["reset"]):
            assert q[j+1] == predecessor(width, 0, q[j]) & z
        for j, states in enumerate(q):
            assert forces(z & states, r["b"][j])
        # The terminal vacuum fixes a white neighboring bit; the opposite claim fails.
        assert not forces(z & q[-1], not r["b"][-1])
        results.append({"word": word, "width": width, "reset": r["reset"],
                        "bound": r["bound"], "passed": True,
                        "wrong_terminal_bit_rejected": True})
    print(json.dumps({"passed": True, "certificates": results,
                      "lean_kernel_verification": False}, indent=2))


if __name__ == "__main__":
    main()
