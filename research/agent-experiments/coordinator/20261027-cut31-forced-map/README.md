# Exact cut-31 forcing for the actual empty-driven Rule 30 gate

This research archive proves the complete boundary and masked forcing left after a cut of31 in the inverse physical reconstruction of the actual empty-driven gate. The gate is `refinedGate r = u empty (155+r)`. The formulas hold for every natural index, including zero, and the reconstructed tail agrees at every depth and time with `zrow (Psi empty)` from physical time311. This is the alternating-driver/right-empty construction; finite support of its reconstructed left start is not assumed, and it has not been identified with the single-seed center orbit.

The new source is [Rule30Cut31ForcedMapResearch.lean](Rule30Cut31ForcedMapResearch.lean), SHA256 `40f5dee5473493137db9c25f10dd76e2051424321ea0c08fc52452ea1df846ca`. Its namespace is `Ruliology.CellularAutomata.Rule30Cut31ForcedMapResearch`; its root module name is intentionally unchanged. The only Lake configuration addition to the pinned core project is a library entry for this root module.

The result retains nonzero forcing. It does not prove that a second cut returns to the same boundary class, that finite support decreases, that `CQ01Empty` holds, or that a Rule30 prize problem is solved. A count of five or six nonzero forcing **ticks** per sufficiently late short-gap event is a paper corollary only. Adjacent ticks need not be separate pulses or episodes.

## Mathematical result

Write `G = refinedGate`, `K_i = G(r+i) AND G(r+i+3)`, `X(k,t) = recon (boundary G) k t`, `B(t)=X(32,t)` and `L(t)=X(31,t) AND NOT X(32,t)`. With `+` denoting XOR, the verified formulas are

```
B(2r)   = 1 + G(r+1) + K1 + K5 + K7 + K8 + K12
B(2r+1) = 1 + K3 + K4 + K7 + K8 + K11 + K13 + K4*K12
L(2r)   = K6 + K7 + K12
L(2r+1) = K7 + K8 + K13 + K5*K13
```

The two quadratic terms matter. The all-depth identity is

```
forcedTail (B refinedGate) (L refinedGate) n t
  = zrow (Psi empty) (t+311) (n+32).
```

No finite-support, supplied temporal period, bi-infinite extension, or local-language hypothesis appears in that actual-history theorem. [PROOF.md](PROOF.md) explains the checked overlap coverage, scalar locality, and physical coordinate map.

## Reproduction

Use Python3 and an already installed Lean4.35.0 toolchain. No Mathlib or other package is required. This archive contains all21 exact sources:14 official sources at pin `7d665044b904117af9e82328aeb90a30692b2b85` and7 research sources. It contains no compiled objects or IR sidecars.

```
python verify.py --audit-only
python verify.py --lean /path/to/lean --lake /path/to/lake
```

On Windows the corresponding executables are `lean.exe` and `lake.exe`. Supply real matching toolchain executables; the script does not install or download a toolchain. If `--lake` is omitted, it is taken beside the selected Lean executable. An optional `--run-name NAME` selects a new output directory under `runs/`; existing run directories are never reused.

The script checks the manifest and source hashes, clears inherited `LEAN_PATH`, copies the exact sources into a new project without `.lake`, and runs `lake build Rule30Cut31ForcedMapResearch`. It invokes the unchanged checker for `DrivenEmptyCore`, `Rule30EmptyGateLanguageResearch`, and the new leaf, with all10 named headlines. It then prints and compares every headline type and axiom list with the independent validation transcript, ignoring only whitespace. Partial checker claims alone do not establish an expected statement; this explicit transcript comparison and the source audits provide that scope check.

For a manual build in a clean copy, the target is `lake build Rule30Cut31ForcedMapResearch`. [SOURCES.json](SOURCES.json) gives all three checker module names and their exact headline arguments. [verify.py](verify.py) contains the complete commands. The project has no external package requirements and never invokes `lake update`.

## Validation and provenance

Independent full-source Lake validation passed. All21 sources were built fresh, with no reference objects or inherited `LEAN_PATH`. The three selected modules passed full replay of401 constants and10 headlines; the new leaf accounts for107 constants and6 headlines. All10 printed types and axiom lists match the author transcripts byte-for-byte. The source build had zero warnings. The recorded build took82.410 seconds; the complete guarded run took100.020 seconds, with peak owned memory1,877,516,288 bytes and no guard stop. Exact raw mathematical receipts are under [evidence/root-full-lake](evidence/root-full-lake); the guard is a clearly labeled resource/timing extract.

The author freshly built and fully replayed the unchanged `DrivenEmptyCore` dependency (276 constants/2 headlines), unchanged gate-language dependency (18/2), and final new leaf (107/6):401 constants and10 headlines. That author run reused18 earlier compiled dependencies after source/object hash checks; it was not a fresh21-source build. The subsequent independent validation is recorded separately. Counts include internal/generated constants.

The unchanged checker SHA256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. The six new headlines depend only on `propext` and `Quot.sound`. Historical failed attempts are retained under [evidence/author](evidence/author): attempt01 had elaboration/rewrite and heartbeat failures, attempt02 had natural-addition normalization failures, and attempt03 passed. The two certificate dependencies passed in attempt01. No failed leaf is counted as a pass.

The prior paper and scalar records are included to document how the formula was found, including the failed unforced reset and adjacent-short-gap interaction. The Lean proof checks its26-word certificate independently of those Python outputs. Original sealed paper wording sometimes says “pulses”; in the five/six count this means nonzero time positions, not distinct contiguous episodes. The research notes do not upgrade a same-history carrier shift to a support-decreasing reset.

[PORTABILITY.json](PORTABILITY.json) records the only evidence transformations: absolute private workspace prefixes in five historical author logs were removed, the private guard command was omitted from one result extract, and a private worker label in the copied author report was replaced with ?remote worker?. Every transformed artifact retains its original hash and a separate portable hash. Diagnostic text, failed-attempt errors, mathematical checker JSON, exact Lean sources, and root mathematical receipts were preserved. Historical author/source-audit statements that the independent root run was pending are superseded by [ARCHIVE-STATUS.json](ARCHIVE-STATUS.json) and the later [root receipt audit](audits/ROOT-FULL-LAKE-AUDIT.md).

Credits: Troy Lowry and OpenAI Codex. This archive records a research result, not a prize submission. No native Wolfram or LeanLink validation is asserted.
