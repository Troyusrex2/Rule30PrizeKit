# Carrier translations and the sign of a support reset

Status: independent paper/source audit. No new trajectory, finite search, Lean build, or public write. All proposed reset conditions below are obligations, not established properties of the actual empty-driven gate.

## 1. Fixed coordinates and exact source facts

Write X(k,t)=zrow L t k, where increasing k means moving farther LEFT from the white wall. The official update is

    X(k+1,t+1) = X(k+2,t) XOR (X(k+1,t) OR X(k,t)).

The official `Rule30ZeroBoundary.zrow_edge` says: if L has a last black cell at depth W>=1, then X has its last black cell at depth W+t at time t. The official `recon_shift` says

    recon a k (t+T) = recon (fun s => a(s+T)) k t.

Thus advancing the boundary trace by T constructs the actual row T steps LATER; it is not a backward-time or support-shrinking operation.

The current carrier data concern the pure period-five gate and a boundary trace of period ten. The saved comparisons establish

    C(k+31,t) = C(k,t+2).

The saved report states this for k>=2. Root's additional boundary comparison C(32,t)=a(t+2), together with C(31,t) implying C(32,t), extends it to k>=1: the latter implication makes the first shifted stencil agree with the zero-wall stencil. This extension is a supplied scalar/source fact, not a new computation or kernel claim in this note. Nothing below needs to assume that the actual empty-driven reconstruction has this identity.

## 2. A full same-history translation contradicts finite support directly

Suppose L is nonzero and finite, and S,T are natural numbers with S+T>0. At ANY fixed time t, the identity

    for every k>=1, X(k+S,t)=X(k,t+T)                         (H)

is impossible. Let W be the last initial black depth. Choose k=W+t+T. The right side is black by zrow_edge. The left side is at depth W+t+T+S, strictly beyond the last black depth W+t at time t, and is white.

Where the shifted tail remains nonempty, the respective outer edges expressed in the coordinate k would be

    W+t-S             and             W+t+T.

The direct witness above avoids truncated subtraction and also covers a cut beyond the entire row. It does not require S>T, or validity at other times. A global k>=K version also contradicts finite support once t is large enough that W+t+T>=K.

Therefore, if a SAME-HISTORY 31/+2 identity were proved at all depths for the actual nonzero finite reconstruction, it would already be a contradiction. It is not an iterative restart with support gain 31-2=29. The two positions compared by (H) separate the outer edges by 31+2=33.

The carrier can satisfy (H) because it is not a finite-support row. The finite-run corridor from `forced-carrier-corridor-20261027T0825` only supplies (H) in a triangular region. A last-black witness is useful only if its depth lies inside that region; global validity cannot be supplied by the carrier computation. The single short-gap defect also falsifies the exact proposed extension of (H) to arbitrary admissible futures.

## 3. A genuine advance-and-cut map has a different equality

A genuine reset into a DIFFERENT member Y has the orientation

    Y(k,t) = X(k+S,t+T),             k>=1, t>=0.             (R)

Here one first advances the physical trajectory by T and then cuts S cells. If the new initial positive-depth row is nonzero, its exact width is

    W_Y = W_X + T - S,

and hence S>T gives a strict decrease. If S>=W_X+T, the cut tail is entirely white at its initial time; a valid reset class must then either exclude that state by a separately proved nonzero condition or settle it as a terminal contradiction. One cannot quietly assign it a positive width.

The distinction is not a syntactic renaming of the carrier's t+2. If the carrier equality holds, performing an actual advance by 2 and cut by 31 gives

    Y(k,t)=C(k+31,t+2)=C(k,t+4),

not C(k,t+2). Conversely, cutting 31 at the SAME time and obtaining the boundary shifted by 2 identifies that cut row with the actual row two steps later, by recon_shift. If such an identification held for a finite nonzero row, section 2 would already exclude it.

For the known physical forced-pair recoding, advancing between short pulses costs T=6+10q and the fixed spatial cut is S=12. Its width change is T-S=10q-6, as the earlier paper states. The pure carrier's 31/+2 comparison does not change that accounting into a reset with cost 2; a new all-time map satisfying (R) would have to be proved.

## 4. The full pair and the seam cannot be discarded

For arbitrary profiles A,B : Nat -> Bool define the forced reconstruction R[A,B] by

    R[A,B](0,t)=A(t),     R[A,B](1,t)=B(t),
    R[A,B](k+2,t)=R[A,B](k+1,t+1)
                    XOR (R[A,B](k+1,t) OR R[A,B](k,t)).

This carries the literal physical recurrence at every positive depth. The boundary at depth zero is A, not automatically white. Let

    A'(t)=R[A,B](S,t+T),   B'(t)=R[A,B](S+1,t+T).

Induction on k gives the exact all-depth identity

    R[A',B'](k,t)=R[A,B](k+S,t+T),             k>=0.

This is the lossless pair reset. Its existence as a definition is automatic; membership of (A',B') in a useful repeatable class with S>T is the missing mathematical content.

If the intended target is instead zero-wall `recon B'`, discarding A' is valid exactly when

    for every t, A'(t) AND NOT B'(t) = false.                (M)

Indeed the depth-two equations differ precisely by that Boolean term. Under (M), all positive depths agree by induction. Conversely equality of the two depth-two histories forces (M). The weaker statement that the mask vanishes inside one carrier corridor is insufficient for an all-time zero-wall reset.

The original forced pair (X12,X13) has mask L=X12 AND NOT X13, whose short-gap pulses are known and generally nonzero. Keeping only L also loses B. A reset into a genuinely forced class is allowed, but its complete pair, phase, and future must be retained.

The edge lemma extends at paper level to forced reconstruction: if its positive initial row has last black depth W>=1, then its last black depth at time t is W+t, irrespective of A. The same induction as zrow_edge proves this: boundary injection cannot outrun an already nonzero edge at positive depth. This extension does NOT say that a zero positive row remains zero under a nonzero boundary.

## 5. A precise sufficient reset condition for CQ01Empty

Here is an exact target, with the finite-support premise excluded from the definition of the class. It is stated to expose the remaining proof obligation, not offered as an achieved reduction.

Let C be a predicate on full profile pairs p=(A,B). Let R_p be the forced reconstruction above. Require:

    (Entry)  C(0,a_*),
             a_*(2r)=NOT G(r), a_*(2r+1)=true,
             G(r)=u empty(155+r).

    (Nonzero)  For every p with C(p), there exists k>=1
               with R_p(k,0)=true.

    (Positive reset)  For every p with C(p), there exist
               S,T : Nat and q=(A_q,B_q) such that
               T<S, C(q), and for every t>=0,
               A_q(t)=R_p(S,t+T),
               B_q(t)=R_p(S+1,t+T).

The class and these properties concern actual full profiles; they must be proved without declaring finite support as part of membership or assuming that a desired reset is physically realizable. The reset may be a computed transformation, and may carry additional phase/defect registers, but those registers must not replace either literal profile. A zero-wall formulation may replace the first pair equality by the proved mask condition (M); it must still establish the exact target reconstruction.

These three conditions imply that no member of C has finite positive support. Proof: among all finite members choose one with minimum last-black depth W, using Nonzero. Apply Positive reset. The forced edge formula gives white values in the new initial row above W+T-S, so the new row is finite. Nonzero for q forces S<W+T and gives a last-black depth W'=W+T-S. Since T<S, W'<W, contradiction. This uses no converse of forward finite-support preservation.

Entry applies to the actual row

    R_(0,a_*)(k,t)=zrow(Psi empty)(311+t,k).

If FinSupp(Psi empty) held, official zrow_fin would give finite support at time 311, hence a finite member of C, contradicting the preceding argument. Therefore the stated conditions are sufficient for CQ01Empty. They are not currently proved. The actual entry row is nonzero without any finite hypothesis: a_*(1)=true, so either its initial depth-one bit is black, or its initial depth-two bit is black by the first inverse stencil.

This criterion does not require all arbitrary 3/5/no33 words to lie in C. It can retain exact empty-right ancestry and additional invariants. Merely defining C by the desired finite-white realization, however, supplies no reset theorem: that realization is the support premise under investigation. A proof conditional on finite support would be legitimate if it independently established strict descent and closure, but naming that premise is not such a proof. The support-independent formulation above cleanly separates the missing structural result from the eventual contradiction argument. The new work must be a class-preserving positive reset, not renaming the reconstruction consistency equations.

## 6. Scope and disposition

The signed-coordinate audit resolves a genuine ambiguity: same-history forward temporal translation has an immediate outer-edge obstruction, whereas a reset after physical waiting has support cost T and requires a different full state. The 31/+2 carrier does not by itself supply the latter map. No claim of CQ01Empty, a new descending class, an upper birth budget, or Problem 1 follows. The active packet lane may seek the concrete reset in section 5; this audit neither computes it nor duplicates that work.
