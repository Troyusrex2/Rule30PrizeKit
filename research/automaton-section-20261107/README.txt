Rule 30 actual singleton: sections and exact positive-word representation length

Read RESULTS.txt first. Problem 1 remains OPEN.
The automaton and moving-center formula are already in the kit; this archive
does not present them as new. The extra checked statement concerns the minimum
positive-word length representing the ENTIRE actual negative half-row on zero
input. It is not a general computational lower bound or a parity theorem.

Reproduce with Python 3 and an existing Lean 4.35.0 installation:
    python replay.py --lean /path/to/lean
No network, installation or Mathlib is needed. The seven project source files
include the unchanged official checker and three public dependencies. replay.py
copies only source into a fresh replay-* directory, builds with one thread and
replays all three owned modules through the official kernel checker. Individual
processes are capped at 60 seconds and total replay at ten minutes.

For the bounded orientation/semantic checks:
    python validate_semantics.py
This overwrites semantic-validation.json with a new timing; preserve the saved
receipt if byte-for-byte manifest verification is needed. Finite checks are not
evidence of aperiodicity. The infinite statements are Lean theorems.

Checks were run locally. This branch is a research archive, not an official
API submission, catalog PR, or claim of Wolfram acceptance. No prize theorem
is claimed. SHA256SUMS.json binds all archived payloads except itself.
