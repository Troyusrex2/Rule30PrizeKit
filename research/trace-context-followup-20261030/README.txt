Finite edge observability / change of right context
Troy Lowry with OpenAI Codex; 2026-10-30. Computational follow-up, not a Lean proof.

One precise stronger claim, still OPEN (QEO):
For W>=1, nonzero a,b<2^W, and 0<=c<W, put
  Phi(x)=x XOR ((x<<1) OR (x<<2)).
If bit(c+t, Phi^t(a))=bit(c+t, Phi^t(b)) for every 0<=t<=2W,
then bit_length(a)=bit_length(b).
Physical position p corresponds to bit c-p initially, and bit c+t-p at time t.
Thus unequal bit lengths are unequal physical left edges. The interval includes
the observer. Every pair of finite rows fits such an interval. A uniform proof
of QEO would imply EdgeObservable and hence official Problem1, using the already
checked Rule30TraceEdge.problem1_of_edgeObservable. QEO may be false; no proof
or infinite-trace counterexample has been obtained.

Fixed bounded tests (all nonzero rows, all unordered pairs tested implicitly
by exact trace-prefix grouping; not a sampled-pair search):
* All observer indices 0..W-1, every width W<=16: no unequal-edge collision
  through time2W. Complete in27.187s. This does NOT prove QEO.
* Balanced observer c=floor(W/2)-1, W<=18: same finite non-refutation.
* Observer c=0, W<=18: same result. This geometry is an elementary positive
  control: with an initially white right half, left-permutivity reconstructs
  the left ray from its trace. It is not a new research theorem.
* Post-hoc maximum-prefix statistics in the registered balanced windows:
  W=11,c=4,a=1329,b=895 first differ at t=21;
  W=12,c=5,a=3105,b=1058 first differ at t=23.
  The latter has left edges-6,-5. These are finite long delays close to2W,
  not asymptotic lower bounds or evidence of infinite equality. Literal
  physical-coordinate CA controls separately validate the selected witnesses.
No larger census is authorized by this experiment's preregistration.

An alternative formulation uses the known realization theorem, not a new
bijectivity discovery. Fix an initial right half R. The map E_R from initial
left-ray bits a_j=x(-j) to the center trace is a compatible family of binary
prefix permutations, by left-permutivity (also covered by the catalog's
Rule30Realization.column_realizable_unique). For contexts R0=all-white and
R1=only physical cell+1 black, T=E_R1^{-1} E_R0 is a rooted-tree automorphism.
EdgeObservable asks for a degree obstruction when both reconstructed rows
are finite, allowing arbitrary finite right contexts. Full row injectivity
is false; the known stripe aliases have the same edge.

A fixed prefix computation of T at16bits gives distinct length8 section
fingerprints at prefix depths0..8:
  1,2,4,7,13,25,49,96,191.
For any deterministic Mealy transducer realizing this T, these distinguishable
sections require at least191 states. This is a finite computational lower
bound; it does NOT prove an infinite-state requirement, nonautomaticity of
the center, or any prize statement. Both encoders are permutations and all
prefix compatibilities were checked. Independent literal controls cover
all512 pairs of8-bit inputs/context choices and256 deterministic16-bit cases.

Important false inference, explicitly corrected during this work:
A finite value T_16(a)=b does not make b the full infinite output. Six small
nonfixed pairs looked like possible finite aliases at16bits; independent
follow-up finds their first disagreements at17,17,32,19,22,19, respectively.
None is an established infinite alias. The pair a=170,b=196 (full packed rows
340,393; observer1) agrees for32 observations and then differs at t=32, despite
common support width9. Both left edges agree. Thus a2W bound for FULL ROW
recovery is false here, while the proposed EDGE bound remains unrefuted by
these tests. Do not conflate these statements.

This package is discovery evidence only. The independently kernel-checked
uniform result from the block is PR58, the classification of homogeneous
finite-range group-valued zero-curvature connections. It rules out that
specific local group-invariant route; it does not rule out all invariants,
noninvertible semigroups, nonlocal mechanisms, or the edge-observability route.

Reproduce each preregistered script directly with Python3; no third-party
dependencies. The probes enforce their own fixed time/width limits. The
follow-up/control scripts are explicitly post-hoc, not preregistered predictions.
