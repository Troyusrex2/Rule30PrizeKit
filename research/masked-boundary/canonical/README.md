# Canonical catalog module replay

This freezes Rule30DrivenMaskTransport in its catalog namespace, with four unchanged official dependencies at932cf8dde039b89b1dcbe9636867bb1b2057fef0. Source is exactly the canonical PR source. The open PeriodicMaskExclusion hypothesis is NOT proved; this is not a prize solution.

Replay with Python3 and official Lean4.35.0:

    python verify.py --lean C:/path/to/lean.exe --out C:/new/empty/output

The fresh focused replay passed28 owned declarations and10 headlines; all five source modules were rebuilt, no owned objects reused, standard axioms only and no research-source warnings. The unchanged official checker is partial-mode, so actual types and explicit type guards are recorded. This is not a whole-catalog or cold standard-library build. The original research-namespace archive is one directory above.
