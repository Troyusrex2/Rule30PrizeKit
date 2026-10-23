"""Generate two smaller endpoint-conditioned refinements of six-bit core bounds."""
import json
from pathlib import Path
import sys
from generate import step, predecessor, mask, DATA, BASE, write

sys.set_int_max_str_digits(200000)


def image(k, a, states):
    return {step(k, a, z, row) for row in states for z in (0, 1)}


def constant(states):
    bits = {s & 1 for s in states}
    assert len(bits) <= 1
    return bool(next(iter(bits), 0))


def match(name, values, typ="Nat"):
    return f"def {name} : Nat → {typ}\n" + "".join(
        f"  | {i} => {str(v).lower() if isinstance(v, bool) else v}\n" for i, v in enumerate(values)) + (
        "  | _ => false\n" if typ == "Bool" else "  | _ => 0\n")


def case_proof(name, variable, bound, proposition, theorem_prefix, count, extra=""):
    text = f"theorem {name} ({variable} : Nat) (h : {variable} {bound}) {extra} : {proposition} := by\n"
    text += f"  have hc : {' ∨ '.join(f'{variable} = {j}' for j in range(count))} := by omega\n"
    text += "  rcases hc with " + " | ".join("rfl" for _ in range(count)) + "\n"
    text += "".join(f"  · exact {theorem_prefix}{j}\n" for j in range(count))
    return text


def main():
    records = []
    for word, k in (("110001", 12), ("111101", 10)):
        z = set(range(1 << k))
        while image(k, 0, z) != z:
            z = image(k, 0, z)
        p = [{0}]
        for a in reversed(word):
            p.append(predecessor(k, int(a), p[-1]))
        p.reverse()
        s = [z]
        for a in word:
            s.append(image(k, int(a), s[-1]))
        q = [p[0]]
        while q[-1] != {0}:
            assert len(q) < 60
            q.append(predecessor(k, 0, q[-1]) & z)
        b = [constant(z & row) for row in q]
        c = [constant(s[j] & p[j]) if a == "0" else False for j, a in enumerate(word)]
        length, reset = len(word), len(q)-1
        stem = "SixTailEndpoint" + word
        ns = BASE + "Rule30SixTailEndpointResearch.C" + word
        defs = stem + "DefsResearch"
        bits = "[" + ",".join("true" if a == "1" else "false" for a in word) + "]"
        text = f"""module
public import {BASE}Rule30RestrictedBackwardTubeResearch
@[expose] public section
namespace {ns}
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30RestrictedBackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := {k}
def L : Nat := {reset}
def tail : List Bool := {bits}
def Z : Nat := {mask(z)}
"""
        for name, rows in (("P", p), ("S", s), ("Q", q)):
            text += match(name, [mask(row) for row in rows])
        text += match("b", b, "Bool") + match("c", c, "Bool")
        text += f"end {ns}\n"
        write(defs, text)
        facts = ["theorem Zzero : Z.testBit 0 = true := by decide +kernel\n",
                 "theorem Zfixed : image K false Z = Z := by decide +kernel\n"]
        facts += [f"theorem p{j} : preCheck K (tail.getD {j} false) (P {j}) (P {j+1}) = true := by decide +kernel\n" for j in range(length)]
        facts += [f"theorem s{j} : image K (tail.getD {j} false) (S {j}) = S {j+1} := by decide +kernel\n" for j in range(length)]
        facts += [f"theorem q{j} : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q {j+1}) (Q {j}) = true := by decide +kernel\n" for j in range(reset)]
        facts += [f"theorem qf{j} : colConst K (Z &&& Q {j}) (b {j}) = true := by decide +kernel\n" for j in range(reset+1)]
        facts += [f"theorem pf{j} : colConst K (S {j} &&& P {j}) (c {j}) = true := by decide +kernel\n" for j, a in enumerate(word) if a == "0"]
        previous, modules = defs, ["Rule30Certificates." + defs]
        for chunk, lo in enumerate(range(0, len(facts), 3)):
            name = stem + f"Checks{chunk}Research"
            text = f"module\npublic import {BASE}Rule30Certificates.{previous}\n@[expose] public section\nnamespace {ns}\nopen Rule30StripCertificates Rule30BackwardTubeResearch\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
            text += "".join(facts[lo:lo+3]) + f"end {ns}\n"
            write(name, text)
            previous = name
            modules.append("Rule30Certificates." + name)
        name = stem + "Research"
        text = f"""module
public import {BASE}Rule30Certificates.{previous}
@[expose] public section
namespace {ns}
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30RestrictedBackwardTubeResearch
"""
        text += case_proof("Pstep", "j", "< 6", "preCheck K (tail.getD j false) (P j) (P (j+1)) = true", "p", 6)
        text += case_proof("Sstep", "j", "< 6", "image K (tail.getD j false) (S j) = S (j+1)", "s", 6)
        text += case_proof("Qstep", "j", f"< {reset}", "Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q (j+1)) (Q j) = true", "q", reset)
        text += case_proof("Qforce", "j", f"≤ {reset}", "colConst K (Z &&& Q j) (b j) = true", "qf", reset+1)
        text += "theorem Pforce (j : Nat) (h : j < 6) (hz : tail.getD j false = false) : colConst K (S j &&& P j) (c j) = true := by\n"
        text += "  have hc : " + " ∨ ".join(f"j = {j}" for j in range(6)) + " := by omega\n  rcases hc with " + " | ".join("rfl" for _ in range(6)) + "\n"
        for j, a in enumerate(word):
            text += f"  · exact pf{j}\n" if a == "0" else "  · simp [tail] at hz\n"
        threshold = max(71, k-1+63, reset)
        text += f"""
theorem no_padding {{x : Int → Bool}} {{lo : Int}}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : {threshold} ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  apply Rule30RestrictedBackwardTubeResearch.no_padding_of_endpoint_tube hlo hzero i tail
    K L Z Q P S b c (by decide) Zzero Zfixed (by rfl) (by rfl) (by rfl) (by rfl)
  · intro d hd; exact Qstep d (by simpa [L] using hd)
  · intro j hj; exact Pstep j (by simpa [tail] using hj)
  · intro j hj; exact Sstep j (by simpa [tail] using hj)
  · intro d hd; exact Qforce d (by simpa [L] using hd)
  · intro j hj hz; exact Pforce j (by simpa [tail] using hj) hz
  · simp [tail]; omega
  · simp [K, tail]; omega
  · simp [L]; omega
end {ns}
"""
        write(name, text)
        modules.append("Rule30Certificates." + name)
        records.append({"word": word, "width": k, "reset": reset, "bound": threshold,
                        "Z": sorted(z), "P": [sorted(row) for row in p], "S": [sorted(row) for row in s],
                        "Q": [sorted(row) for row in q], "b": b, "c": c, "modules": modules})
    (Path(__file__).parent / "endpoint-certificates.json").write_text(json.dumps(records, indent=2)+"\n", encoding="utf-8", newline="\n")
    print("Generated two endpoint refinements with sufficient bounds 74 and 72")


if __name__ == "__main__":
    main()
