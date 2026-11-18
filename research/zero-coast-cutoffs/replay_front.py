"""Run the kit checker in an empty temporary project using this checkout's sources."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="Lean executable from lean-toolchain")
    args = parser.parse_args()
    lean = shutil.which(args.lean)
    if not lean:
        parser.error(f"Lean executable missing: {args.lean}")
    here = Path(__file__).resolve().parent
    kit = here.parents[1]
    dependencies = [
        "Rule30Jen", "Rule30Diagonals", "Rule30Prize", "Rule30MaskedJen",
        "Rule30BlackRuns", "Rule30DrivenLeft", "Rule30PeriodTwo", "Rule30ZeroBoundary",
    ]
    modules = [Path("Ruliology/CellularAutomata", name + ".lean") for name in dependencies]
    modules.append(Path("ReverseFront.lean"))
    names = [
        "step_iff_zrow", "base_steps", "base_time", "sample_steps", "legal_entry",
        "propagation", "arbitrary_predecessors", "prescribed_step", "prescribed_front", "alternate_entry",
        "compact_time", "compact_tail", "compact_steps", "compact_differs", "compact_trace",
        "advance_local", "advance_bound", "six_table", "six_returns", "six_merge_iff",
    ]
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        env = dict(os.environ, LEAN_PATH=directory)

        def run(*options):
            process = subprocess.run(
                [lean, "-j1", "-M3072", *options], cwd=root, env=env,
                stdout=subprocess.PIPE, encoding="utf-8", timeout=120,
            )
            if process.returncode:
                raise RuntimeError(process.stdout)
            return process.stdout

        for module in modules:
            source = here / module if module.name == "ReverseFront.lean" else kit / "lean" / module
            (root / module).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, root / module)
            run("-o", module.with_suffix(".olean"), module)
        shutil.copyfile(kit / "Check.lean", root / "Check.lean")
        headlines = [arg for name in names for arg in ("--headline", "ReverseFront." + name)]
        output = run("--run", "Check.lean", "ReverseFront", "--claim", "partial", *headlines)
        receipt = json.loads(output.strip().splitlines()[-1])
        if receipt["verdict"] != "pass":
            raise RuntimeError(receipt)
        print(json.dumps(receipt, indent=2, ensure_ascii=True))


if __name__ == "__main__":
    main()
