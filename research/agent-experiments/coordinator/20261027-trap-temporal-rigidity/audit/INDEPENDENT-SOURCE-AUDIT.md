# Independent canonical source and validation audit

Verdict: source, proof preservation, theorem scopes, and saved validation receipts PASS. One documentation clarification is identified below. This reviewer performed no Lean build, dynamics, public poll, or publication. The fresh canonical and Lake runs were performed by the root coordinator; their receipts were subsequently reviewed independently.

Exact integrated source hashes:

* `Rule30PeriodicHalfline.lean`: `842edbbf3aef6c2b949b80937fe971737a17e936d6dd26080ff2da219c00b76f`.
* `Rule30TrapPeriod21.lean`: `959f423c2319f4d56fab923f7db52b86c17080cd0555225e1df83a093a2e0d36`.
* Unchanged `Rule30Period21Profiles.lean`: `2f00a1755f210c020883fd6767485488ca723826721f89bfa5856a012657f46f`.
* Unchanged `Rule30Certificates/TrapPeriod21.lean`: `0bb6834c784e0ef3c1033c6e8a1fbaf7d886098a2503ea0cd02c99cfca9faae2`.

## Independent body and layout comparison

All42 prepared payload hashes/lengths matched the integration manifest `183183ccb726db8cf0b61ba09e578ad3e42d8d4f92bc209e59fb2498ade1b16b`; the14-file candidate inventory also matched. This review independently reconstructed all five body segments from the four frozen research sources rather than relying only on preparation-script assertions. Their before/after hashes agree with `BODY-MAP.json`, and the resulting bodies agree exactly with the canonical files after the documented replacements.

The onset body is unchanged. The generic rigidity prefix changes only namespace opens to reflect colocation and to remove an unused family open. The eventual21 body changes its onset open. The family rigidity suffix changes the qualified eventual21 theorem reference. The pair-trace body changes its generic open and renames `trapped_pairs_eventually_distinct` to `trapped_pairs_differ_arbitrarily_late`. That rename changes neither the theorem's type nor its proof. No tactic, hypothesis, conclusion, or proof term was otherwise changed.

The original public profile and certificate files are byte-identical. Removing the single new public import from the original-length prefix of the family file recovers its complete old bytes. All appended proofs occur afterward. Eight official dependency sources also agree byte-for-byte with the baseline Git objects. The aggregator changes only by adding the generic module import. The README diff changes one family row and adds one generic row, apart from line-ending normalization.

The module graph is acyclic. `Rule30PeriodicHalfline` directly imports only the profile helpers and official `Rule30Ether`; it does not import the numeric trap certificate or trap family. The family imports that generic module alongside its original certificate and official trap imports. All12 source modules are covered by the recorded topological order. No research-module or Mathlib import remains. The four contribution modules use the existing `module`, public-import, and `@[expose] public section` conventions. Declarations lie in their intended canonical namespaces; previous physical declarations remain in `.Physical`. No private declaration, unchecked axiom, unsafe proof replacement, or hidden command was introduced.

## Actual theorem scope

All32 printed canonical headline types and their axiom lists were read. The generic representative preserves absolute time phase and permits separate unbounded column onsets. Finite-code inverse-chain rigidity requires code injectivity only on the chain. Head-period propagation retains one common positive period; no period-divisibility assumption is introduced.

The strongest family theorem retains actual physical `IsR30`, a prescribed eventual001 boundary with its onset T, a valid actual t001 strip entry at `t1>=T`, and mod3 label/phase alignment. It concludes that for every j<k and every time bound B, some t>=B has unequal adjacent-pair values. There is no exterior temporal-period or finite-support premise. “Arbitrarily late” does not mean inequality at every sufficiently late time, and no witnessing-time bound or preselected differing component is supplied.

The separate common-period theorem excludes any ONE positive period shared eventually by all columns, allowing different onsets. The old fixed21 interfaces remain present and checked. None of these theorems proves trap absorption, fixed-column aperiodicity, a uniform theorem over all driver words, or a Rule30 prize statement. Unbounded individual column periods remain possible.

Documentation clarification: the reviewed candidate's new family README row abbreviates the assumptions to “an actual right half entering any correctly aligned t001 state.” The explicit eventual001 boundary must also be retained in publication wording; aligned entry alone does not prescribe future forcing. The root coordinator accepted this correction for a publication overlay while preserving the sealed integration inputs, with separate old/new documentation hashes and a patch. This audit does not claim a readback of that later overlay. The underlying theorem types and proofs are correct and require no rebuild for that wording change.

## Root-run fresh canonical validation

At the initial mechanical-review stage the transformed sources had no merged-source kernel verdict. The subsequent exact root-run receipts close that validation requirement. The fresh runner creates an empty private library, replaces external LEAN_PATH with that library, and compiles all12 source modules under Lean4.35.0. No Mathlib or precompiled contribution/reference cache is used. All12 build logs are empty. The unchanged official checker hash is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`; its own deprecation warning remains in raw checker logs.

Fresh RESULT SHA256: `569fbd6a4956b3e765020c8bda8ee981f18ef62e6fdededfca33161b917977c7`. Each raw checker JSON matches that receipt, with full replay PASS, importsStatements true, matching headlines, and no new axioms. The four actual counts are:

| Module | Replayed constants | Non-internal | Internal | Headlines |
|---|---:|---:|---:|---:|
| Rule30Period21Profiles | 58 | 34 | 24 | 3 |
| Rule30Certificates.TrapPeriod21 | 624 | 417 | 207 | 4 |
| Rule30PeriodicHalfline | 52 | 27 | 25 | 11 |
| Rule30TrapPeriod21 | 80 | 36 | 44 | 14 |
| Total | 814 | 514 | 300 | 32 |

These are module-owned constants, including generated constants and the existing certificate; they are not814 new handwritten theorems. The fresh guard completed with exit0 in27.4896447 seconds, peak823373824 bytes, and minimum available44855955456 bytes, within300 seconds/8GiB/2GiB minimum free.

The separate actual targeted Lake build and required strongest-head checker invocation also passed, on unchanged source hashes. Its RESULT SHA256 is `3ce53a47a5398752f760fae0faec358986fdcba4df62310d0374ab664aebb169`. It replays80 family constants and checks the one required `trapped_pairs_differ_arbitrarily_late` headline; this80/1 check is not added to the814/32 total. The build and check took14.6862629 and1.7385104 seconds. Its guard completed with exit0 in16.5144619 seconds, peak840314880 bytes, and minimum available44837814272 bytes.

Both validations are root-run evidence audited here, not reviewer executions. The exact source preservation, all32 current types, complete fresh replay, and separate Lake invocation support canonical integration once the publication wording retains the full driver premise.
