"""Replay exact notebook source in a PRIVATE, prepared pinned worktree.

Replaces Rule30Submission.lean there. Does not evaluate or submit a notebook.
Build Rule30PrizeKit first.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kit", type=Path, required=True)
    parser.add_argument("--lake", required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--headline", action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    kit, output = args.kit.resolve(), args.output.resolve()
    pinned = "cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554"
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=kit, text=True).strip() == pinned
    checker = (kit / "Check.lean").read_bytes().replace(b"\r\n", b"\n")
    assert checker == subprocess.check_output(["git", "show", "HEAD:Check.lean"], cwd=kit).replace(b"\r\n", b"\n")
    source = "import Rule30PrizeKit\n" + args.source.read_text(encoding="utf-8")
    output.mkdir(parents=True, exist_ok=True)
    (kit / "Rule30Submission.lean").write_text(source, encoding="utf-8", newline="\n")
    begin = time.monotonic()
    commands = [["build", "Rule30Submission"], ["env", "lean", "--run", "Check.lean", "Rule30Submission", "--claim", "partial"]]
    for headline in args.headline:
        commands[1] += ["--headline", headline]
    report = None
    for name, command in zip(("build", "check"), commands):
        result = subprocess.run([args.lake] + command, cwd=kit, capture_output=True,
                                encoding="utf-8", errors="replace", timeout=600)
        raw = result.stdout + result.stderr
        (output / (name + ".log")).write_text(raw, encoding="utf-8", newline="\n")
        if result.returncode:
            raise RuntimeError(raw[-8000:])
        if name == "check":
            report = next(json.loads(line) for line in raw.splitlines() if line.startswith('{"claim"'))
    assert report["verdict"] == "pass" and report["replay"]["ok"]
    (output / "check.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    summary = {"passed": True, "kit_commit": pinned,
               "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
               "checker_sha256": hashlib.sha256(checker).hexdigest(),
               "root_import_included": True, "replayed_constants": report["replay"]["constants"],
               "headlines": args.headline, "seconds": round(time.monotonic() - begin, 2),
               "notebook_evaluated": False, "prize_api_submission": False}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
