# Closing legal temporal pasts beside the white wall

The main unconditional result is spatial-tail agreement for **every legal infinite future** when editing four, five, six, or seven gate bits of past. The bounds are columns 38, 49, 99, and 107 respectively. The future need not be periodic, and its reconstructed row need not be finite. The earlier three-bit result is in PR47; this contribution's proof does not depend on that PR.

The gate convention is a_G(2r)=NOT G(r), a_G(2r+1)=true, with every little-endian eight-bit gate window in S={8,9,16,18,33,36,66,72,132,144}. Rows use official Rule30ZeroBoundary.recon/lam. Legal pasts mean the complete prepended gate also satisfies this language.

**The all-length claim remains open.** Rule30GateTailReduction proves that checked finite prefix covers for every past length would exclude finite rows in this gate class. The width-preservation step, a 40-step legal splice between every pair of the ten gate states, and the periodic-prefix/Jen-clock argument are all proved. The theorem explicitly retains the unproved FiniteCoverFamily or AllPastClosing premise. It is not a proof of a Rule30 Prize statement.

Other proved components:

* Two equal adjacent spatial columns of the entire finite temporal past strip, together with a shared future, force permanent spatial merging.
* A packed-word certificate check implies the literal cell recurrence; a sound finite prefix tree covers all infinite legal continuations.
* Legal ten-bit pasts 132 and 528 of one common eventual-gap5 future differ at column 200. This refutes the proposed 20n closing rate, not eventual closing.

## Validation

The canonical catalog adaptation passed a fresh **13-source dependency build** and unchanged official Check.lean replay of all five new source modules, including the generated certificate module: **3,057 declarations and 37 headline/type checks**, no new axioms or source warnings, no reused objects. This was a focused dependency build, not a whole-catalog build. Most declarations in the generated module are auxiliary finite-check terms, not separate mathematical discoveries.

Official pin: 932cf8dde039b89b1dcbe9636867bb1b2057fef0. Lean 4.35.0. Check.lean is unchanged. `evidence/RESULT.json` records every source hash, individual checker result, and selected theorem type; `evidence/Types.log` lists the types and axiom sets. The resource receipt records the owned-process guard. PROVENANCE.json distinguishes the initial research sources from the LF canonical sources and certificate-namespace adaptation.

## Reproduce

Supply the official Lean 4.35.0 Windows executable and a new output directory:

    python lean-certificate/verify.py --lean <path-to-lean.exe> --out <new-directory>

The verifier checks the executable and input hashes, builds all dependencies afresh, runs the unchanged checker on every new module, and performs a combined-import/type smoke check. It reuses no prebuilt proof objects.

Regenerate every numerical leaf triangle, the two rate-counterexample triangles, and check all 100 bridge paths using only the Python standard library:

    python regenerate_data.py

The independent literal truth-table/complete-prefix auditor is under certificates/. Run it there with the supplied four certificate filenames. That audit is additional evidence; the Lean proofs do not trust Python or SAT. Computational covers through length 12, which are not all Lean-proved here, are in the earlier immutable [experiment archive](https://github.com/Troyusrex2/Rule30PrizeKit/tree/b32a065fdeddcf622386a5d4cc4864ab838c2fe7/research/past-strip-cover).

MANIFEST.json hashes every payload; scoped Git attributes preserve exact validated bytes. No Prize claim or cloud submission is made by this archive.
