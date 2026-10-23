"""Serialize builds and official kernel replays across the research dependency chain."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.stderr.reconfigure(encoding="utf-8", errors="replace")

ROOT = Path(__file__).resolve().parents[2]
BASE = "Ruliology.CellularAutomata."


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default=shutil.which("lake"))
    parser.add_argument("--kit", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path, default=Path(__file__).parent / "evidence/catalog")
    parser.add_argument("--target", default=BASE + "Rule30SixTailResearch")
    parser.add_argument("--build-only-base", help="Compile, but do not repeat replay of modules present at this catalog commit")
    parser.add_argument("--resume", action="store_true", help="Reuse an unchanged checked prefix from this output directory")
    args = parser.parse_args()
    if not args.lake:
        parser.error("Use --lake PATH or put Lean 4.35.0 on PATH")
    kit = args.kit.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    order, seen = [], set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        path = kit / "lean" / Path(*module.split(".")).with_suffix(".lean")
        text = path.read_text(encoding="utf-8")
        for dependency in re.findall(r"^(?:public )?import (\S+)", text, re.M):
            if dependency.startswith(BASE) and dependency.endswith("Research"):
                visit(dependency)
        order.append((module, path))

    visit(args.target)
    checker = (kit / "Check.lean").read_bytes().replace(b"\r\n", b"\n")
    original = subprocess.check_output(["git", "show", "HEAD:Check.lean"], cwd=kit).replace(b"\r\n", b"\n")
    assert checker == original, "Check.lean changed"
    prior = {}
    if args.resume and (output / "summary.json").exists():
        prior_summary = json.loads((output / "summary.json").read_text(encoding="utf-8"))
        if prior_summary.get("checker_sha256") == hashlib.sha256(checker).hexdigest():
            prior = {row["module"]: row for row in prior_summary["checks"]}
    reuse_prefix = bool(prior)
    results = []
    summary = {"passed": False, "checker_sha256": hashlib.sha256(checker).hexdigest(),
               "checks": results, "target": args.target,
               "base_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=kit, text=True).strip(),
               "notebook_evaluated": False, "prize_api_submission": False}

    def save():
        (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")

    def run(command, log, expected_codes=(0,)):
        result = subprocess.run([str(args.lake)] + command, cwd=kit / "lean", capture_output=True,
                                encoding="utf-8", errors="replace", timeout=600)
        raw = result.stdout + result.stderr
        (output / log).write_text(raw, encoding="utf-8", newline="\n")
        if result.returncode not in expected_codes:
            print(raw[-12000:], flush=True)
            raise RuntimeError(f"Failed: {command}")
        return raw

    for index, (module, path) in enumerate(order, 1):
        begin = time.monotonic()
        source_hash = hashlib.sha256(path.read_text(encoding="utf-8").encode()).hexdigest()
        if reuse_prefix and module in prior and prior[module].get("source_sha256_lf") == source_hash:
            results.append(prior[module])
            save()
            print(f"[{index}/{len(order)}] {module.rsplit('.', 1)[-1]}: unchanged checked prefix", flush=True)
            continue
        reuse_prefix = False
        run(["build", module], module + ".build.log")
        relative = path.relative_to(kit).as_posix()
        if args.build_only_base and subprocess.run(
                ["git", "cat-file", "-e", args.build_only_base + ":" + relative],
                cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0:
            row = {"module": module, "base_build_only": True,
                   "source_sha256_lf": hashlib.sha256(path.read_text(encoding="utf-8").encode()).hexdigest(),
                   "seconds": round(time.monotonic()-begin, 3)}
            results.append(row)
            save()
            print(f"[{index}/{len(order)}] {module.rsplit('.', 1)[-1]}: base compiled ({row['seconds']}s)", flush=True)
            continue
        raw = run(["env", "lean", "--run", str(ROOT / "research/six-tail/InspectModule.lean"), module], module + ".inspect.log")
        metadata = next(json.loads(line) for line in raw.splitlines() if line.startswith('{"'))
        if not metadata["constants"]:
            row = {"module": module, "constants": 0, "no_local_declarations": True}
        elif not metadata["theorems"]:
            raw = run(["env", "lean", "--run", "../Check.lean", module, "--claim", "partial"],
                      module + ".check.log", expected_codes=(1,))
            report = next(json.loads(line) for line in raw.splitlines() if line.startswith('{"claim"'))
            assert report["replay"]["ok"] and report["newAxioms"] == [], module
            assert report["reasons"] == ["--claim partial needs at least one --headline"], module
            (output / (module + ".check.json")).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
            row = {"module": module, "constants": report["replay"]["constants"],
                   "kernel_replay_passed": True, "data_only_module": True,
                   "submission_headline_not_applicable": True}
        else:
            headlines = metadata["theorems"][:1]
            if module in (BASE + "Rule30SixTailResearch", BASE + "Rule30SixTailSharpenedResearch"):
                headlines = [module + "." + name for name in (
                    "no_six_tail_leftFinite", "no_six_tail_finite", "no_six_tail_seed")]
            command = ["env", "lean", "--run", "../Check.lean", module, "--claim", "partial"]
            for headline in headlines:
                command += ["--headline", headline]
            raw = run(command, module + ".check.log")
            report = next(json.loads(line) for line in raw.splitlines() if line.startswith('{"claim"'))
            assert report["verdict"] == "pass" and report["replay"]["ok"], module
            (output / (module + ".check.json")).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
            row = {"module": module, "constants": report["replay"]["constants"], "passed": True}
        row["source_sha256_lf"] = hashlib.sha256(path.read_text(encoding="utf-8").encode()).hexdigest()
        row["seconds"] = round(time.monotonic() - begin, 3)
        results.append(row)
        save()
        print(f"[{index}/{len(order)}] {module.rsplit('.', 1)[-1]}: passed ({row['seconds']}s)", flush=True)
    summary["passed"] = True
    save()


if __name__ == "__main__":
    main()
