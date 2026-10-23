# Windows notebook build notes

Both research notebooks have now been evaluated in Wolfram Engine 15.0.0, with
Lean 4.35.0 and the verifier's pinned kit. Their saved input cells preserve the
exact checked UTF-8 source; their saved outputs contain successful kernel replays
and no message cells. Reports live under each research directory's
`evidence/wolfram-notebook/`. Separate prize-system verifier verdicts now pass too; sanitized reports are included alongside the local evidence.

## LeanLink's Windows bridge

The official LeanLink 1.2.1 Windows DLL failed to load (Windows error 127). The
1.2.2 download reproduced the same error. An import-table inspection found a
descriptor requesting 91 functions from `libleanshared.dll` that it does not
export in Lean 4.35.0. Rebuilding the unchanged upstream C/Lean sources with the
Lean SDK's LLVM linker, directly against all four runtime DLLs and without the
bundled `libgnu_lean_thunks.a`, produced a working bridge.

The tested upstream source is
`WolframInstitute/LeanLink@7141f02905dfc26d94dddc663c9e27a228a84959` (version 1.2.2).
This is a local development build, not a new official Wolfram release. No Lean
kernel, theorem source, axiom policy, or official checker was patched. The valid
starter theorem passes replay; the forged `debug.skipKernelTC` example is rejected.

`rebuild-shim.py --help` lists the explicit SDK/source/header paths. It builds the
upstream Lean library, links the shim, and checks that Windows loads it. Tested
header sets were Windows SDK UCRT 10.0.22621.0 and MSVC 14.41.34120. The rebuilt DLL
was placed in the development paclet's `LibraryResources/Windows-x86-64/` and
loaded with `PacletDirectoryLoad` in the evaluation processes. No installed paclet
files were overwritten.

LeanLink also expects the pinned SDK in an Elan layout. For the existing portable
compiler, an isolated `ELAN_HOME` containing a toolchain-directory junction was
passed to those processes. The compiler and runtime are the same verified release;
the user's default toolchain was not changed.

## Notebook builder fixes

- The converter evaluates a document in a private `MTNB$...` context. The builder
  locates that document's environment and rejects an absent or ambiguous result.
- The notebook saves its genuine `KernelCheck` result in `rule30KernelCheck`.
  This checks the whole declaring module once. The builder validates that result
  and every headline's theorem kind and permitted axioms, avoiding duplicate
  imports/replays that retain large native environments in memory.
- The source preflight compares the notebook's held Wolfram string literal with
  the exact UTF-8 file bytes. Binary reading preserves the final newline that
  Windows text import dropped in this environment.
- `RULE30_MARKDOWN_CONVERTER_SOURCE` optionally selects the public converter's
  local `.wl` source. The tested source SHA256 before one progress-print
  instrumentation line was
  `e0a3c417f19ebe25357b9f9565661d2feac9e50284dc09943a84c8711722da5c`.
  `UseCache -> False` forces actual evaluation.

The official starter was evaluated in four fresh processes (positive theorem,
axiom-gap audit, forged-proof rejection, and catalog examples), preserving its
executable demonstrations while releasing memory between independent cases. A
single combined run was stopped when available memory became too low. Both
research notebooks were each evaluated as one complete document in a fresh kernel.

No account identifiers, authentication codes, credentials, or raw login logs are
included in these artifacts. Troy Lowry provided the author name and explicit consent. Both submissions now
pass the prize system's automated verifier; human review remains pending.
