# A uniform obstruction to finite-window birth-consuming potentials

Paper proof only, using the exact 84-column/6-time physical cycle audited in single-column-period-rigidity-paper-20261027T0730. No trajectory, search, solver, or Lean build was run in this phase. The conclusion concerns a precisely stated finite-history local inequality; it is not a counterexample to any assertion restricted to an all-time eventually periodic single-seed center.

## 1. Exact finite-history formulation

Let F be physical Rule 30 on integer sites,

    F(x)(j) = x(j-1) XOR (x(j) OR x(j+1)).

For a finite initial row z write Z(t,j)=F^t(z)(j). For t>=4 define

    d_z(t) = Z(t,1) XOR Z(t-4,1),
    b_z(t) = 1 if d_z(t)=0 and d_z(t+1)=1, and 0 otherwise.

This is the same backward-time mismatch/birth convention as Rule30PhysicalDefects.mismatch and trueBirth at Q=4. Those catalog definitions themselves use the actual single-seed cell function; d_z and b_z here are explicitly their arbitrary-row counterparts, not a claim that the existing Lean declaration has already been generalized.

For any natural radius R, let

    O_R(z,t) = ( (Z(t,j))_|j|<=R,
                 (Z(t-4,j))_|j|<=R,
                 t mod 4 ).

The coordinates in both windows are in the same physical frame. There is no moving or sheared coordinate. Let LocalAlt(z,t) mean

    Z(s,0) = (s mod 2) for every integer s in [t-4,t+1].

All these times are natural when t>=4. This particular phase is enough; allowing both alternating phases only broadens the premise.

**Uniform obstruction.** For EVERY R>=0 there is NO real-valued function E on these observations such that, for every nonzero finite z and every t>=4 satisfying LocalAlt(z,t),

    E(O_R(z,t+1)) + b_z(t) <= E(O_R(z,t)).        (1)

In particular there is no such nonnegative potential. Nonnegativity is not used: the contradiction is a closed observation loop with positive total birth cost. The same proof refutes a rule required only on the twelve steps t=4,...,15 of every finite history whose center alternates on the entire interval [0,16].

## 2. The fixed infinite witness and exact birth phases

The previously audited physical spacetime X is defined for all integer times and sites by a six-bit profile table repeated every 84 sites. Its center and right-neighbor words are respectively

    c(t) = 010101 repeated,
    r(t) = 001101 repeated.

Every column has temporal period 6. All 504 physical scalar stencils and all 84 pair overlaps were independently checked in the sealed source phase. Its exact construction and input hash are retained there; this proof does not repeat or enlarge the computation.

The backward mismatch d(t)=r(t) XOR r(t-4) has the following exact table:

| t modulo 6 | 0 | 1 | 2 | 3 | 4 | 5 |
| --- | --- | --- | --- | --- | --- | --- |
| r(t) | 0 | 0 | 1 | 1 | 0 | 1 |
| r(t-4)=r(t+2) | 1 | 1 | 0 | 1 | 0 | 0 |
| d(t) | 1 | 1 | 1 | 0 | 0 | 1 |
| b(t)=[d(t)=0,d(t+1)=1] | 0 | 0 | 0 | 0 | 1 | 0 |

Thus in the HALF-OPEN source interval [4,16), the births are exactly t=4 and t=10. Their new mismatches occur at 5 and 11. The endpoint t=16 is not a source step in the telescope. This avoids confusing forward-shift and backward-shift birth conventions.

## 3. One finite initial row for every radius

For arbitrary R>=0 set M=R+20 and define

    z_R(j) = X(0,j) when -M<=j<=M, and 0 otherwise.

This is finitely supported. It is nonzero because X(0,-1)=1 (the audited left-neighbor profile is 59, with bit 0 equal to 1), and -1 lies inside every such cutoff.

The exact physical light-cone theorem says that a cell at time s and site j depends only on initial sites [j-s,j+s]. In the official core source this is Rule30ZeroBoundaryBarriers.evol_local:

    equality on [a,b] implies equality at (s,j)
    whenever a+s<=j and j+s<=b.

Rule30Equivalents.AlgebraicDegree.evol_congr gives the equivalent direct [j-s,j+s] statement. No finite-support or periodicity hypothesis is needed for this locality step.

For 0<=s<=16 and |j|<=R, the entire cone lies in [-R-16,R+16], hence in [-M,M]. Therefore

    Z_R(s,j) = X(s,j) for 0<=s<=16 and |j|<=R.   (2)

The birth variable separately reads site 1, even when R=0. Its largest necessary time is 16, and its cone lies in [-15,17]. Since 17<=R+20, the same cutoff also gives

    Z_R(s,1) = X(s,1) for every 0<=s<=16.        (3)

The center is in the observed window for every R, so it alternates through time 16. Every LocalAlt(z_R,t) holds for 4<=t<=15. All older times are nonnegative: t-4 ranges from 0 to 11, and at the final observation time 16 the older row is time 12. Computing b_z(15) reads times 15,11,16,12, all covered by (3).

Padding R+20 is deliberately generous. It exceeds both the R+16 observation requirement and the independent radius-17 birth requirement; no endpoint is inferred outside the available cone.

## 4. Closing the local observation loop and telescoping

Since every X column is 6-periodic, it is also 12-periodic. Equations (2) and (3) give

    O_R(z_R,16) = O_R(z_R,4),

because the newer rows are X(16)=X(4) on the window, the older rows are X(12)=X(0), and 16 mod 4 = 4 mod 4 = 0.

The table in section 2 and (3) give

    sum_(t=4)^15 b_z_R(t) = 2.

If (1) held on these twelve legitimate finite-history steps, addition would cancel the intermediate E terms and yield

    E(O_R(z_R,16)) + 2 <= E(O_R(z_R,4)).

The endpoint equality reduces this to 2<=0, a contradiction. R was arbitrary; this is one uniform light-cone proof for all finite radii, not a census of radii or a new finite instance for each radius.

## 5. Exact limits of the obstruction

The proof excludes a potential whose time-varying inputs are ONLY the two fixed-radius physical row windows and phase modulo 4, required to consume every true Q=4 birth for all finite histories satisfying the stated finite-window center condition. It also excludes any deterministic feature extraction of those observations, since such a potential composes to a function E of O_R.

It does NOT refute an inequality whose applicability requires the center to be eventually periodic for ALL future time. Only alternation through time 16 has been proved for z_R; no all-time or eventual-period claim about that finite row is supplied.

It does NOT refute a potential using the whole evolving finite row, an unbounded ancestry record, or the actual position of its finite-support fronts/cutoff relative to the observation. The finite full orbit is not a closed loop: if its left edge at time 0 is l, the official left-edge law places it at l-4 and l-16 at the two endpoints. Those edges differ even though O_R agrees. A potential that can see that missing information is outside (1).

It does NOT refute an inequality restricted to the actual single-seed trajectory. The finite witnesses here are cuts of the 84-periodic row, not asserted to be single-seed ages. Coherence has only the relevant stated meaning: BOTH compared rows are ages t and t-4 of ONE actual finite initial row.

There is no claim against every finite-state proof, every conditional potential, or every certificate with a boundary reserve. The obstruction is the exact observation loop and universal local-step quantifiers above. There is no new Lean verification or public submission in this phase.
