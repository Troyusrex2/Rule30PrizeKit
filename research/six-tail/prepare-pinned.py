"""Copy the research closure into a private pinned worktree, adapting wrappers only."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PINNED = "cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554"
BASE = "Ruliology.CellularAutomata."


def main():
    p = argparse.ArgumentParser()
    p.add_argument("kit", type=Path)
    p.add_argument("--target", default=BASE + "Rule30SixTailResearch")
    a = p.parse_args()
    kit = a.kit.resolve()
    assert kit != ROOT and subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=kit, text=True).strip() == PINNED
    out = Path(__file__).parent / "evidence/pinned-adaptation.json"
    previous = {}
    if out.exists():
        previous = {row["file"]: row["pinned_sha256_lf"] for row in json.loads(out.read_text())["files"]}
    seen, rows = set(), []

    def copy(module):
        if module in seen:
            return
        seen.add(module)
        relative = Path("lean") / Path(*module.split(".")).with_suffix(".lean")
        source = (ROOT / relative).read_text(encoding="utf-8")
        for dep in re.findall(r"^public import (\S+)", source, re.M):
            if dep.startswith(BASE) and dep.endswith("Research"):
                copy(dep)
        adapted = re.sub(r"^module\s*\n", "", source, count=1)
        adapted = re.sub(r"^public import ", "import ", adapted, flags=re.M).replace("@[expose] public section", "")
        target = kit / relative
        if target.exists() and target.read_text(encoding="utf-8") != adapted:
            old_hash = hashlib.sha256(target.read_text(encoding="utf-8").encode()).hexdigest()
            if previous.get(relative.as_posix()) != old_hash:
                raise RuntimeError(f"Refusing to overwrite different existing source: {target}")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(adapted, encoding="utf-8", newline="\n")
        rows.append({"file": relative.as_posix(), "catalog_sha256_lf": hashlib.sha256(source.encode()).hexdigest(),
                     "pinned_sha256_lf": hashlib.sha256(adapted.encode()).hexdigest()})

    copy(a.target)
    out.write_text(json.dumps({"kit_commit": PINNED, "wrapper_changes_only": True, "files": rows}, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"Prepared {len(rows)} modules without changing proof bodies")


if __name__ == "__main__":
    main()
