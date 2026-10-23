"""Check that both essays embed exactly the independently checked Lean source."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
CASES = [
    ("forbidden-suffix", "Rule30SuffixStandalone.lean", "Rule30-Forbidden-Suffix-Addendum.md"),
    ("six-tail", "Rule30SixCoreStandalone.lean", "Rule30-Six-Core-Notebook.md"),
]


def main():
    for directory, source_name, essay_name in CASES:
        here = ROOT / "research" / directory
        source = "import Rule30PrizeKit\n" + (here / source_name).read_text(encoding="utf-8")
        essay = (here / essay_name).read_text(encoding="utf-8")
        match = re.search(r'LeanImportString\[("(?:\\.|[^"\\])*")', essay)
        assert match, essay_name
        assert json.loads(match[1]) == source, essay_name
        summary = json.loads((here / "evidence/notebook-source/summary.json").read_text(encoding="utf-8"))
        assert summary["passed"] and summary["root_import_included"]
        assert summary["source_sha256"] == hashlib.sha256(source.encode()).hexdigest()
        assert not summary["notebook_evaluated"] and not summary["prize_api_submission"]
        print(essay_name + ": embedded source round trip and pinned kernel-check hash match")


if __name__ == "__main__":
    main()
