"""Build the binary prefix cover and generate its Lean proof.

The finite search proposes a spatial depth at each leaf. The Lean checker
establishes what this depth implies, including arbitrary infinite futures.
"""
from dataclasses import dataclass
import argparse
from pathlib import Path


@dataclass
class Node:
    length: int
    word: int
    index: int | None
    children: tuple = ()

    @property
    def size(self):
        return 1 if self.index is not None else sum(c.size for c in self.children)


def find_depth(n, word):
    a, b = word, word ^ 1088
    left_a = left_b = 0
    for j in range(min(n - 11, 174) + 1):
        if ((left_a ^ left_b) | (a ^ b)) & 2047 == 0:
            return j
        left_a, a = a, (a >> 1) ^ (a | left_a)
        left_b, b = b, (b >> 1) ^ (b | left_b)
    return None


def build(n=17, word=65470, level=0):
    j = find_depth(n, word)
    if j is not None:
        return Node(n, word, j)
    if level == 24:
        raise ValueError("Uncovered path at the fixed depth limit")
    return Node(n, word, None, tuple(
        build(n + gap, word ^ (((1 << (gap - 1)) - 1) << n), level + 1)
        for gap in (6, 10)
    ))


def lean_tree(node):
    if node.index is not None:
        return f"(.hit {node.index})"
    l, r = node.children
    return f"(.fork {lean_tree(l)} {lean_tree(r)})"


def generate(root):
    lines = [
        "module", "public import Ruliology.CellularAutomata.Rule30ResetSwapCore", "",
        "/-! Kernel-checked prefix cover for the first six/ten reset swap: 1272 leaves and at most 24 further gaps. -/",
        "", "@[expose] public section",
        "namespace Ruliology.CellularAutomata.Rule30ResetSwap.Certificate",
        "open Ruliology.CellularAutomata.Rule30ResetSwap", "",
        "set_option maxRecDepth 16000", "set_option maxHeartbeats 16000000", "",
        "-- Each leaf supplies a candidate synchronization depth to the kernel-checked verifier.",
    ]

    def emit(node, label):
        if node.size <= 16:
            term = lean_tree(node)
            proof = "by decide +kernel"
        else:
            l, r = node.children
            emit(l, label + "s")
            emit(r, label + "l")
            term = f".fork {label}s {label}l"
            proof = f"Bool.and_eq_true_iff.mpr ⟨{label}s_ok, {label}l_ok⟩"
        lines.extend([
            f"def {label} : Tree := {term}",
            f"theorem {label}_ok : valid {label} ({node.length},{node.word}) = true :=",
            f"  {proof}", "",
        ])
    emit(root, "cover")
    lines.extend(["end Ruliology.CellularAutomata.Rule30ResetSwap.Certificate", ""])
    return "\n".join(lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--check", type=Path, help="compare with a catalog data module")
    action.add_argument("--write", type=Path, help="write the generated data module")
    args = parser.parse_args()
    root = build()
    if args.check and args.check.read_text(encoding="utf-8") != generate(root):
        raise SystemExit("Certificate source differs")
    if args.write:
        args.write.write_text(generate(root), encoding="utf-8")
    print(f"{root.size} leaves, {2*root.size-1} nodes")
