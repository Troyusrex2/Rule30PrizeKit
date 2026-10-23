"""Rebuild the self-contained catalog proof and the unevaluated essay source."""

import json
from pathlib import Path
import re

from verify import BASE, MODULES, REPO, legacy

HERE = Path(__file__).resolve().parent

WRAPPERS = """
namespace Rule30Submission
open Ruliology.CellularAutomata
open Rule30ForbiddenSuffixCertificatesResearch

theorem no_padding_suffix011 {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+41 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix011)) :=
  Rule30SuffixFamiliesResearch.no_padding_suffix011_leftFinite hlo hzero i v r hr

theorem no_padding_suffix001001 {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix001001)) :=
  Rule30SuffixFamiliesResearch.no_padding_suffix001001_leftFinite hlo hzero i v r hr

theorem no_padding_suffix111001 {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix111001)) :=
  Rule30SuffixFamiliesResearch.no_padding_suffix111001_leftFinite hlo hzero i v r hr

end Rule30Submission
"""


def main():
    parts, imports = [], []
    for name, _ in MODULES:
        relative = Path("lean") / Path(*(BASE + name).split(".")).with_suffix(".lean")
        source = (REPO / relative).read_text(encoding="utf-8")
        for imported in re.findall(r"^public import (\S+)", source, re.M):
            if not imported.endswith("Research") and imported not in imports:
                imports.append(imported)
        body = re.sub(r"^import .*\n", "", legacy(source), flags=re.M).strip()
        parts.append("/- Source: " + relative.as_posix() + " -/\n" + body)
    source = "\n".join("import " + item for item in imports)
    source += "\n\n" + "\n\n".join(parts) + "\n" + WRAPPERS
    (HERE / "Rule30SuffixStandalone.lean").write_text(source, encoding="utf-8", newline="\n")

    # The notebook source adds the official root import. Local kernel evidence
    # covers the standalone catalog source; Wolfram/LeanLink has not run here.
    notebook_source = "import Rule30PrizeKit\n" + source
    essay = (HERE / "essay-template.md").read_text(encoding="utf-8")
    essay = essay.replace("@@LEAN_SOURCE@@", json.dumps(notebook_source, ensure_ascii=False))
    (HERE / "Rule30-Forbidden-Suffix-Addendum.md").write_text(essay, encoding="utf-8", newline="\n")
    print(f"Bundled {len(MODULES)} modules and submission wrappers; {len(source.encode())} bytes")


if __name__ == "__main__":
    main()
