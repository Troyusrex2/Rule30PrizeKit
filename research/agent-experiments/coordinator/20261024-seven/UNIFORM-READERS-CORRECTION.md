# Reader archive byte correction

The initial reader-search publication at `f6bc311` normalized some Windows
checkpoint JSON line endings when Git staged them. Its manifest had been
computed from the original archive bytes. The scientific JSON values, the
Lean source and its successful full kernel replay are unchanged.

The correction restores the original checkpoint and worker source bytes,
uses a scoped `* -text` archive attribute, and provides
`universal-reader-artifacts-v2.json` as the current manifest. The first
manifest is retained unchanged for provenance. The correction changes no
numerical conclusion or theorem. The exact staged bytes and all original
source/seed hashes are rechecked before the correcting commit.
