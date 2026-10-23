"""Generate exact backward-vacuum certificates; Lean checks every transition.

The packed updater is a search implementation, not a proof oracle. The independent
checker uses cellwise Boolean updates, and the generated Lean uses official stripStep.
"""
import itertools
import json
from pathlib import Path
import sys

sys.set_int_max_str_digits(200000)
ROOT = Path(__file__).resolve().parents[2]
CATALOG = ROOT / "lean/Ruliology/CellularAutomata"
DATA = CATALOG / "Rule30Certificates"
SEARCH = {
    "100001": 11, "100011": 5, "100101": 7, "100111": 8,
    "101001": 8, "101011": 5, "101101": 10, "101111": 6,
    "110001": 14, "110011": 5, "110101": 7, "110111": 8,
    "111001": 5, "111011": 5, "111101": 12, "111111": 6,
}
BASE = "Ruliology.CellularAutomata."


def step(width, driver, right, row):
    return (((row << 1) | driver) ^ (row | (row >> 1) | (right << (width - 1)))) & ((1 << width) - 1)


def predecessor(width, driver, targets):
    return {row for row in range(1 << width)
            if step(width, driver, 0, row) in targets or step(width, driver, 1, row) in targets}


def mask(states):
    return sum(1 << row for row in states)


def write(name, text):
    path = DATA / (name + ".lean")
    path.write_text(text, encoding="utf-8", newline="\n")


def main():
    assert set(SEARCH) == {"1" + "".join(w) + "1" for w in itertools.product("01", repeat=4)}
    records = []
    for word, width in SEARCH.items():
        backwards = [{0}]
        for bit in reversed(word):
            backwards.append(predecessor(width, int(bit), backwards[-1]))
        padding = 0
        while backwards[-1]:
            backwards.append(predecessor(width, 0, backwards[-1]))
            padding += 1
            assert padding < 100
        states = list(reversed(backwards))
        length = padding + len(word)
        name = "SixTailBackward" + word
        namespace = BASE + "Rule30SixTailCertificatesResearch.C" + word
        defs = name + "DefsResearch"
        bits = "[" + ",".join("true" if b == "1" else "false" for b in word) + "]"
        text = f"""module

public import {BASE}Rule30BackwardVacuumResearch

@[expose] public section

/-! Generated exact predecessor sets for `0^{padding} {word}` at width {width}.
The target is the vacuum; the initial predecessor set is empty. -/
namespace {namespace}
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := {width}
def N : Nat := {padding}
def tail : List Bool := {bits}
def Q : Nat → Nat
"""
        text += "".join(f"  | {j} => {mask(s)}\n" for j, s in enumerate(states))
        text += f"  | _ => 0\nend {namespace}\n"
        write(defs, text)
        modules = ["Rule30Certificates." + defs]
        chunk_size = 2 if width >= 13 else 4
        previous = defs
        for chunk, lo in enumerate(range(0, length, chunk_size)):
            chunk_name = name + f"Steps{chunk}Research"
            text = f"""module
public import {BASE}Rule30Certificates.{previous}
@[expose] public section
namespace {namespace}
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
"""
            for j in range(lo, min(lo + chunk_size, length)):
                text += (f"theorem step{j} : preCheck K "
                         f"((List.replicate N false ++ tail).getD {j} false) "
                         f"(Q {j}) (Q {j+1}) = true := by decide +kernel\n")
            text += f"end {namespace}\n"
            write(chunk_name, text)
            modules.append("Rule30Certificates." + chunk_name)
            previous = chunk_name
        final = name + "Research"
        text = f"""module
public import {BASE}Rule30Certificates.{previous}
@[expose] public section
namespace {namespace}
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : {" ∨ ".join(f"j = {j}" for j in range(length))} := by simp [N, tail] at hj; omega
  rcases hc with {" | ".join("rfl" for _ in range(length))}
"""
        text += "".join(f"  · exact step{j}\n" for j in range(length))
        threshold = max(71, width + 63, padding)
        nproof = "(by simp [N])" if padding == 0 else "(by simp [N]; omega)"
        text += f"""
/-- Uniform column exclusion, for every padding length at least {threshold}. -/
theorem no_padding {{x : Int → Bool}} {{lo : Int}}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : {threshold} ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r {nproof} (by simp [tail]; omega) (by simp [K, tail]; omega)
end {namespace}
"""
        write(final, text)
        modules.append("Rule30Certificates." + final)
        records.append({"word": word, "width": width, "white_steps": padding,
                        "sufficient_padding": threshold, "predecessor_sets": [sorted(s) for s in states],
                        "modules": modules})
    (Path(__file__).parent / "certificates.json").write_text(
        json.dumps(records, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"Generated {len(records)} certificates in {sum(len(r['modules']) for r in records)} modules")


if __name__ == "__main__":
    main()
