"""Rebuild upstream LeanLink's Windows bridge with the pinned Lean SDK's LLVM.

Uses unmodified upstream C/Lean sources and avoids the bundled GNU import-thunk
archive. Requires Windows x64, Lean 4.35.0, Wolfram headers, and Windows SDK headers.
"""
import argparse
import ctypes
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("lean-sdk", "leanlink-source", "wolfram-install", "ucrt-include", "msvc-include", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    sdk, source = args.lean_sdk.resolve(), args.leanlink_source.resolve()
    version = subprocess.check_output([str(sdk / "bin/lean.exe"), "--version"], text=True)
    if "version 4.35.0," not in version:
        parser.error("This recipe was tested with Lean 4.35.0")
    subprocess.run([str(sdk / "bin/lake.exe"), "--dir", str(source / "Native"),
                    "build", "LeanLink:static"], check=True)
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [str(sdk / "bin/clang.exe"), "--sysroot", str(sdk), "-nostdinc",
               "-isystem", str(sdk / "include/clang"), "-I", str(sdk / "include"),
               "-isystem", str(args.ucrt_include.resolve()),
               "-isystem", str(args.msvc_include.resolve()),
               "-fms-extensions", "-ffreestanding", "-D_M_X64=100",
               "-I", str(args.wolfram_install.resolve() / "SystemFiles/IncludeFiles/C"),
               "-shared", "-O2", str(source / "Native/shim/leanlink_shim.c"),
               str(source / "Native/.lake/build/lib/leanlink_LeanLink.a")]
    command += [str(sdk / "bin" / name) for name in
                ("libleanshared.dll", "libleanshared_1.dll", "libleanshared_2.dll", "libInit_shared.dll")]
    command += ["-L", str(sdk / "lib"), "-Wl,--enable-auto-import", "-fuse-ld=lld", "-o", str(output)]
    subprocess.run(command, cwd=source, check=True)
    with os.add_dll_directory(str(sdk / "bin")):
        ctypes.WinDLL(str(output))
    print(json.dumps({"WindowsLoaderPassed": True,
                      "SHA256": hashlib.sha256(output.read_bytes()).hexdigest(),
                      "UpstreamCommit": subprocess.check_output(
                          ["git", "rev-parse", "HEAD"], cwd=source, text=True).strip()}))


if __name__ == "__main__":
    main()
