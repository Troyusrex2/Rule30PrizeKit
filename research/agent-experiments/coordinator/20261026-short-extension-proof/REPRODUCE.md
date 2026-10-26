# Reproduction

Use Lean 4.35.0 and kit commit5473ffd075f63c9d626e63b8455805d4831b39ca in a private project. Verify the unchanged checker hash from summary.json. Build and fully replay in this order:

1. CedarSafetySoundness, CedarSafetySemantics, CedarSafetyBridge.
2. RootShortExtensionCore, RootShortExtensionCases, RootShortExtensionCertificate, RootShortExtension.
3. CedarWhiteTransport, RootD3Reduction.

The first seven sources are under work/worker; the last two are under work/root. Exact module names, declaration namespaces and selected headlines are in work/root/replay.py and the reports. Do not replace full Check.lean replay with an axiom-only audit. The worker delivery's REPRODUCE.md and dependencies.json record its original seven-module run. The root runner was extended with the last two targets after its initial seven-source freeze; the Lean source bytes were unchanged.

The historical Windows runners expect private G913 folders and the pinned read-only reference. Adjust paths for another machine without changing the checker or source statements. No compiled binary caches are published. No full catalog-root build was claimed.

Run `python -B verify_artifacts.py` to audit the retained source/report links, immutable worker delivery, guards, exact scope and prior evidence hashes. Add --staged to audit Git's staged bytes. These evidence checks do not themselves rerun Lean.
