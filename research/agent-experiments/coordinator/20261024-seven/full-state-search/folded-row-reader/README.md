# Full finite configurations read from the center outward

This changes the task from inverse anti-diagonals to complete physical
spatial configurations. Every before and after word retains both finite
halves, paired at equal distance from a black center. The actual center
flips 1->0->1; reward is one per double step. Initial left halves are finite
prefixes of Psi(R), so controlled finite runs exist. No infinite-support
configuration is used. Train left widths32..128; validation256; test512.
Validation and test have fresh mathematical right seeds. Packed physical
evolution was checked against literal Rule30 truth tables and three exact
folded-transducer checks per trace. A finite fit is never a universal rank.
The retained NPZ filename is an inherited training interface, not a claim
that these are the earlier both-white anti-diagonal edges. Selection is
training only; CPU double precision and untouched deep tests are required.
