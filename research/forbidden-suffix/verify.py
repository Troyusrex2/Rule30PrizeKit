"""Build and replay the complete new dependency chain with unchanged Check.lean.

Run from any directory. Only core Lean is needed, not Mathlib. For the verifier's
legacy kit, pass a separate worktree with --kit PATH --prepare-pinned. The latter
copies only the seven listed modules and changes only module-system wrappers.
It refuses to overwrite different existing files.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

REPO = Path(__file__).resolve().parents[2]
PINNED = "cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554"
MODULES = [
    ("Rule30FiniteStripsResearch", "not_eventually_word_strip"),
    ("Rule30WhitePaddingResearch", "padding_strip"),
    ("Rule30WhitePulseResearch", "white_padding_forces_early_white"),
    ("Rule30WhitePaddingVacuumCriterionResearch", "enc_nonzero_has_black"),
    ("Rule30ForbiddenSuffixResearch", "no_padding_of_forbidden_suffix"),
    ("Rule30Certificates.ForbiddenSuffixResearch", None),
    ("Rule30SuffixFamiliesResearch", None),
]
BASE = "Ruliology.CellularAutomata."


def sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def legacy(text):
    text = re.sub(r"^module\s*\n", "", text, count=1)
    text = re.sub(r"^public import ", "import ", text, flags=re.M)
    return text.replace("@[expose] public section", "")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kit", type=Path, default=REPO)
    parser.add_argument("--lake", default=shutil.which("lake"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--prepare-pinned", action="store_true")
    args = parser.parse_args()
    if not args.lake:
        parser.error("lake is not on PATH; use --lake /path/to/lake")
    kit = args.kit.resolve()
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=kit, text=True).strip()
    if args.prepare_pinned and (kit == REPO or commit != PINNED):
        parser.error("--prepare-pinned requires a separate worktree at the exact pinned commit")
    output = (args.output or Path(__file__).parent / "evidence" /
              ("pinned" if args.prepare_pinned else "catalog")).resolve()
    output.mkdir(parents=True, exist_ok=True)
    sources = []
    for name, _ in MODULES:
        relative = Path("lean") / Path(*(BASE + name).split(".")).with_suffix(".lean")
        source = (REPO / relative).read_text(encoding="utf-8")
        target = kit / relative
        expected = legacy(source) if args.prepare_pinned else source
        if args.prepare_pinned:
            if target.exists() and target.read_text(encoding="utf-8") != expected:
                raise RuntimeError(f"Refusing to overwrite different existing file: {target}")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(expected, encoding="utf-8", newline="\n")
        if target.read_text(encoding="utf-8") != expected:
            raise RuntimeError(f"Source mismatch: {target}")
        sources.append({"file": relative.as_posix(), "catalog_sha256": sha(source),
                        "checked_sha256": sha(expected)})
    checker = kit / "Check.lean"
    committed_checker = subprocess.check_output(["git", "show", "HEAD:Check.lean"], cwd=kit)
    if checker.read_bytes().replace(b"\r\n", b"\n") != committed_checker.replace(b"\r\n", b"\n"):
        raise RuntimeError("Check.lean differs from the kit commit")

    def run(arguments, log):
        start = time.monotonic()
        result = subprocess.run([str(args.lake), *arguments], cwd=kit / "lean",
                                encoding="utf-8", errors="replace",
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
        (output / log).write_text(result.stdout, encoding="utf-8", newline="\n")
        if result.returncode:
            print(result.stdout, file=sys.stderr)
            raise RuntimeError(f"Command failed: {arguments}")
        return result.stdout, round(time.monotonic() - start, 3)

    _, build_seconds = run(["build", BASE + "Rule30SuffixFamiliesResearch"], "build.log")
    print(f"Build passed ({build_seconds}s)", flush=True)
    reports = []
    for name, theorem in MODULES:
        module = BASE + name
        if name == "Rule30Certificates.ForbiddenSuffixResearch":
            headlines = [BASE + "Rule30ForbiddenSuffixCertificatesResearch." + t
                         for t in ("safe011", "safe001001", "safe111001")]
        elif name == "Rule30SuffixFamiliesResearch":
            headlines = [module + "." + t for t in (
                "no_padding_suffix011_leftFinite", "no_padding_suffix001001_leftFinite",
                "no_padding_suffix111001_leftFinite", "no_padding_suffix011_finite",
                "no_padding_suffix011_seed", "no_padding_suffix001001_seed",
                "no_padding_suffix111001_seed")]
        else:
            headlines = [module + "." + theorem]
        command = ["env", "lean", "--run", "../Check.lean", module, "--claim", "partial"]
        for headline in headlines:
            command += ["--headline", headline]
        raw, seconds = run(command, name + ".check.log")
        report = next(json.loads(line) for line in raw.splitlines()
                      if line.startswith('{"claim"'))
        if report.get("verdict") != "pass" or not report.get("replay", {}).get("ok"):
            raise RuntimeError(f"Kernel replay failed: {module}")
        (output / (name + ".check.json")).write_text(json.dumps(report, indent=2) + "\n",
                                                    encoding="utf-8", newline="\n")
        reports.append({"module": module, "seconds": seconds,
                        "replayed_constants": report["replay"]["constants"], "verdict": "pass"})
        print(f"Kernel replay passed: {name} ({seconds}s)", flush=True)
    summary = {"passed": True, "kit_base_commit": commit,
               "pinned_legacy_wrappers": args.prepare_pinned,
               "checker_sha256": hashlib.sha256(committed_checker).hexdigest(),
               "lean": subprocess.check_output([str(Path(args.lake).with_name(
                   "lean.exe" if str(args.lake).endswith(".exe") else "lean")), "--version"],
                   text=True).strip(),
               "sources": sources, "source_hash_line_endings": "LF",
               "build_seconds": build_seconds, "checks": reports,
               "notebook_built_or_evaluated": False, "prize_api_submission": False}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
