# Finite-past closing: complete covers, a failed rate, and verified strip lemmas

This archive contains three separate results. It does not solve a Rule30 Prize problem.

* **Lean-checked:** the finite-past absorbing-pair principle and a concrete counterexample to the proposed closing bound20n. The supplied legal ten-bit pasts share a legal infinite future, but their reconstructed rows differ at spatial column200. Fresh nine-source build and unchanged official checker replay:70 declarations, five headline checks, no new axioms, no warnings. Source SHA256: c3d8e1ae0c9febc0da7a93702507c0f0a09cd806ee3ff65ea546524f81ac6ffb.
* **Computational, not Lean-checked:** complete finite prefix covers show closing for every legal future at each fixed past length3 through12. A separate literal truth-table implementation checks every leaf and the completeness of the legal-prefix tree. See MATHEMATICS.md for bounds and limitations, and ALL-AUDITS.json for exact counts/hashes. No arbitrary-n extrapolation is justified.
* **Independent audit of another author's work:** PR49 at d5059d0a174596c9fac771a0b9473defcb9cda6c passed a fresh four-source build and unchanged-checker replay:81 declarations/two headlines. This confirms the paired-periodic-column white-run bounds; their hypotheses exclude finite-left-edge configurations, as the author states. The audit is not a claim of authorship.

The code convention is official Rule30ZeroBoundary.recon/lam. Gate windows are little-endian. Read MATHEMATICS.md before using the data. Explicit row differences at a finite position refute a proposed uniform rate, not eventual tail equality. The counterexample future eventually has gap5 and therefore belongs to a previously proved closing subclass.

## Reproduce

The independent cover auditor uses only Python's standard library:

    python -X utf8 -B audit.py n3-CERTIFICATE.json n4-CERTIFICATE.json n5-CERTIFICATE.json n6-CERTIFICATE.json n7-CERTIFICATE.json n8-cap128-CERTIFICATE.json n9-cap128-CERTIFICATE.json n10-cap200-CERTIFICATE.json n11-cap220-CERTIFICATE.json n12-cap240-CERTIFICATE.json

The n12 audit alone checks576,783,724 literal inverse cells and took about88 seconds on the original machine. The discovery script additionally uses psutil for resource guards. Its documented caps are part of the experiment; caps are never reported as proofs.

To replay the formal module, provide the official Lean4.35.0 Windows executable (the verifier checks its hash) and a new output directory:

    python lean-certificate/verify.py --lean <path-to-lean.exe> --out <new-directory>

The verifier builds every dependency from the supplied pinned sources, reuses no objects, and runs the unchanged Check.lean. The official pin is932cf8dde039b89b1dcbe9636867bb1b2057fef0. The portable audit of PR49 is analogous under pr49-independent-replay/. This is a focused dependency build, not the whole catalog.

MANIFEST.json hashes every payload. Discovery protocol/history files retain the original hypotheses, including the explicitly refuted20n proposal. No cloud submission or Prize claim is made by this archive.
