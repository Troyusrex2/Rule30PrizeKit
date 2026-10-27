# Final static audit of the physical-birth catalog contribution

**PASS.** The reviewed candidate consists of two new canonical modules and exactly two added catalog README rows. This audit ran no Lean, Lake, Wolfram, trajectory calculation, or remote command, and changed no candidate source or public file.

The candidate was reviewed on branch `contribution/physical-birth-local-potential-20261027`, with base `7d665044b904117af9e82328aeb90a30692b2b85`. The existing PR40 worktree was clean when inspected.

## Exact source preservation

* `Ruliology.CellularAutomata.Rule30PeriodicBirthCounterexample`: SHA256 `feb16ec4ddd636f751a5984d23093d18409355df1c8d38f594b5a151774f9632`, unchanged from the previously audited canonical source.
* `Ruliology.CellularAutomata.Rule30LocalBirthPotential`: SHA256 `5107b675eecbb5b5b21831167eaa9290e49b1e984484ac1eb10435317e00fa3b`. Its bytes are exactly the frozen research source `369377cab23bff97d686bcf9441be04069bede425b8d28ac2494b4e5c0bba984` after adding `module`, making the two imports public, adding the exposed public section, and changing the enclosing namespace and closing `end`. No mathematical body changes.

All twelve worktree sources and private validation-project sources match INPUTS and RESULT hashes. The ten official dependencies equal the pinned Git blobs. The Lake configuration and toolchain file also equal the pin. The checker is unchanged, SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

All seventeen freshly printed headline types and axiom lists match the previously audited types after only namespace qualification and whitespace normalization. This comparison checks the actual printed statements; a partial-result checker's `typeMatches` flag alone does not compare against a separately supplied expected theorem type.

## README and mathematical scope

Removing exactly the two new rows restores the pinned README byte-for-byte. The periodic-example row correctly states a period-2 center, period-6 right neighbor, N distinct coherent backward-four mismatch births before time 6N, and infinite initial support. It does not present a finite-seed example.

The local-potential row correctly states every finite radius, integer-valued potential, the current and four-ticks-earlier physical windows, and phase modulo 4. It retains the universal finite-nonzero-configuration quantifier and the finite local alternating-center condition. It explicitly excludes whole-row, ancestry-dependent, and single-seed-only potentials from its conclusion. The source likewise does not supply an all-time periodic center for the finite cutoff or exclude a rule whose applicability requires that stronger premise.

The earlier source audits cover the all-integer physical recurrence, Nat-subtraction endpoints, radius-zero observation, finite cutoff, locality, and the closed observation loop. The unchanged canonical bodies preserve those conclusions. Neither module proves or disproves Prize Problem 1.

## Fresh validation evidence

The reviewed phase is `physical-birth-publication-validation-20261027T0755`. Its validator asserts that the new project has no `.lake` directory, clears inherited LEAN_PATH, selects the pinned toolchain, verifies all twelve source hashes, and invokes actual Lake build on the two new targets. The project has no external package dependencies or reference object overlay. The saved build log explicitly lists all twelve source modules as built and ends successfully.

The unchanged checker then runs through `lake env` on each new module. Both raw JSON results equal their entries in RESULT:

| Contribution | Full kernel replay | Named headlines | Verdict |
| --- | ---: | ---: | --- |
| Periodic birth counterexample | 44 constants | 10 | PASS |
| Local birth potential | 45 constants | 7 | PASS |

Thus the run freshly builds twelve sources and fully replays **89 contribution constants / 17 headlines**. This is not a claim that all ten official dependency modules were separately replayed in this run. No new axioms or nonstandard dependencies are reported; all named headlines succeed. Source compilation has zero warnings. The unchanged checker's known replay-API deprecation warning remains in the raw checker logs.

The Lake build took 18.4468118 seconds. The full guarded invocation exited zero after 21.7897411 seconds, with no guard stop; peak sampled owned RSS was 1,862,021,120 bytes and minimum sampled available memory was 43,945,197,568 bytes. The limits were 300 seconds, 8 GiB owned RSS, and 2 GiB minimum available memory. These numbers are transcribed from the reviewed root receipt, not from a duplicate audit run.

The validator records all twelve new object hashes and rechecks every source after validation. The local audit payload contains source and receipts, not these remote fresh binaries: their hashes were reviewed as recorded provenance, not independently rehashed locally. This limitation does not change the byte-level source/body comparisons or the raw successful build/check/type evidence.

No source, scope, or evidence correction is requested. The earlier author-manifest IR-file exclusion remains a portable-packaging matter and does not alter this candidate or its validation.
