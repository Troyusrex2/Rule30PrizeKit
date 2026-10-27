# Exact cut-31 defect packets and the forced boundary code

Status: paper identities supported by two fixed scalar controls and a separately owned exhaustive local-function check. No new Lean theorem is claimed. The single-defect and two-defect controls are prescribed histories, not the actual empty gate or finite-left realizations. The uniform formula below applies by language coverage and reconstruction locality, not by extrapolating either control's trajectory.

## 1. Cut, shield, and coordinates

Use X0=0, X1=a and the exact inverse physical recurrence

    X_(k+2)(t)=X_(k+1)(t+1)+(X_(k+1)(t) OR X_k(t)),

with XOR written as +. For the period-five gate, a(2r)=1-G(r), a(2r+1)=1. The root's saved period-10 carrier pair at index31 is

    (X32,X31)=(767,682).

Here767 is the temporal +2 shift of the input profile1022, and682 AND NOT767=0. The latter is a shield condition, not a literal zero older column. It implies the pure-carrier reset extends to k>=1.

For any history define the cut-31 boundary data

    A=X31, B=X32, L=A*(1+B), delta(t)=B(t)+a(t+2).

These retain the complete effect of the older column on the remaining tail: Z_k=X_(31+k) obeys

    Z1=B,
    Z2(t)=B(t+1)+B(t)+L(t),
    Z_(k+2)(t)=Z_(k+1)(t+1)+(Z_(k+1)(t) OR Z_k(t)), k>=1.

Thus B and L determine the full remaining reconstruction, not just its observed head. A is only needed through L because A OR B=B+L. Dropping L when it is nonzero changes the actual recurrence.

The shear used here is ONLY the coordinate substitution u=t+2, with Btilde(u)=B(u-2). It is not a support-rank descent or an advancing different-class reset. A same-history carrier identity with spatial31 and temporal+2 does not authorize charging a restart cost2.

## 2. Full single-defect packet

The fixed input has black gate events ..., -5,0,3,8,13,... . It agrees with the past period-five phase at scalar boundary times t<=5, and with the future phase at times t>=1. Since X32 reads only a[t..t+31], both delta and L vanish outside[-25,0]. This is an all-time locality bound; the finite computation is only needed inside it. The previously suggested[-30,5] bound is valid but conservative.

Exact scalar extraction gives

    supp(delta)={-25,-24,-21,-16,-15,-14,-13,-10,-7,-5,-2},
    supp(L)={-25,-24,-15,-14,-13,-12}.

The 52 A/B cell values were compared between an array recurrence and a separate memoized scalar recurrence. The identity

    delta(t+1)+delta(t)+L(t)=X33(t)+X2(t+2)

matches root's entire saved base-depth2 residual exactly. No larger rectangle was computed: the new cone uses only input[-25,31] through depth32.

After shear u=t+2, the delta support is

    {-23,-22,-19,-14,-13,-12,-11,-8,-5,-3,0},

and forcing support is

    {-23,-22,-13,-12,-11,-10}.

Btilde has odd-time zeros at{-23,-19,-13,-11,-5,-3}. Outside the packet its odd values are1, while its even values vary on the carrier. Consequently no temporal translation, even combined with a two-periodic XOR gauge, makes one parity constant. In particular this defect does not return to the old unforced odd-black boundary class. It instead supplies an explicit larger forced boundary class.

## 3. The one authorized adjacent-defect interaction

The only added history has short starts0 and8: black events ..., -5,0,3,8,11,16,... . Its full packet lies in[-25,16]. Compare it with XOR sums of the single packets translated by physical0 and16. The complete interaction is

    delta interaction: one bit at t=-7;
    L interaction:     one bit at t=-9.

Both are odd-time corrections. There are no even-time corrections. The two-history extraction used input[-25,47] through depth32 and 84 independent scalar cell comparisons. Before computing, locality already bounded the interaction to[-9,0]: the two-defect input agrees with the first single defect through boundary time21 and with the translated second single defect from time1 onward.

No other defect separation, period, or depth was tested in this phase. The single-control source and its result were preserved unchanged when the second protocol was frozen.

## 4. Why distant or third defects do not invalidate the local formula

Here the complete gap language means bi-infinite gates with black events unbounded in both directions, successive black gaps3 or5, and no successive gaps33. It does not include an all-white gate by a vacuous gap condition. Consecutive short starts are separated by3+5q, q>=1, so physical short-start spacing is at least16. A short start e can affect this cut's residual at time t only in its active interval

    2e-25 <= t <= 2e.

The cone is a[t..t+31]. A short start earlier than this active range has already selected its future carrier phase throughout the cone; a later one does not alter the past carrier within the cone. This does not mean its phase is discarded: anchor the local carrier to the black event immediately before the first active short gap. Its residue fixes the phase. The five-gaps before/after the active defects then agree with that phase until the next active switch.

At most two active intervals can contain t, since they have width25 and their starts are separated by at least16. If two do, their gate-index separation is less than13; among possible short-start separations3+5q, it must be8. The alternatives for the exact local cone are therefore a pure carrier, a translated one-defect cone, or the translated starts0,8 cone. Defects outside this set can change the chosen carrier phase but not the anchored local pattern. This is the missing justification for using the finite packets as a uniform code rather than assuming nonlinear superposition.

For example q>=3 gives physical separation at least36, so every local cone has at most one active defect and the single packets are disjoint. q=2 gives separation26 and also no active-interval overlap. q=1 is exactly the interaction computed above. Three short starts cannot be active together.

Root supplied an independent exhaustive local-function check in `cut31-local-event-map-20261027T0840`: an eight-state countdown automaton generates all26 legal length17 gate words. Its state(d,g) has g in{3,5},0<=d<g; at a black state d=0, g is the just-completed gap and next gap3 is allowed only after5. Every state reaches(0,5), and that state reaches all eight, so every path extends in both directions. Conversely every complete legal gate gives such a path. For each word,33 scalar boundary bits suffice for X31/X32 at times0,1. Starting with X1 and performing31 triangular updates gives X32, with the retained older column X31. All26 outputs match the formulas below. This phase reviewed that source and coverage argument but did not rerun the26-word computation.

For a one-sided gate, the formula applies at every window belonging to this complete gap language. There is a stronger checked interface for the actual refined gate G(r)=u empty(155+r): Rule30EmptyGateLanguageResearch.windowWord_allowed puts EVERY eight-window, including r=0, in the literal list[8,9,16,18,33,36,66,72,132,144]. These words use bit0 for the earliest time. The seven-bit overlap equation w_next=(w>>1)+128*b gives exactly the graph

    8,9 ->132 ->66 ->33;
    33 ->16 ->8, or33 ->144 ->72 ->36 ->18 ->9.

Every vertex reaches33, and33 reaches every vertex. The only black output vertices are9 and33; their possible successive black paths have lengths5 or3, and the length3 path from9 to33 cannot follow another length3 path. Thus this graph describes complete3/5/no33 gate histories. The actual overlapping eight-windows give a right-infinite path, and strong connectivity extends that path leftward without changing any actual nonnegative gate bit. Consequently every actual17 window is in the complete language, at every r>=0. This derivation uses the existing checked eight-window theorem and the displayed literal overlap graph; it does not assume a uniform prehistory of the actual gate or infer an initial black event from spacing alone.

## 5. Uniform full boundary formula

Set K_i=G(r+i)G(r+i+3), and g_i=G(r+i), for a legal window G(r),...,G(r+16). Then the complete cut boundary is

    B(2r)   =1+g_1+K_1+K_5+K_7+K_8+K_12,
    B(2r+1) =1+K_3+K_4+K_7+K_8+K_11+K_13+K_4 K_12,
    L(2r)   =K_6+K_7+K_12,
    L(2r+1) =K_7+K_8+K_13+K_5 K_13.

The even formulas are the isolated-packet sums. The odd products are exactly the pair interactions at physical-7 and-9 relative to the earlier short start. Root's exhaustive check found only two failures of the isolated formula: the B-odd correction and the L-odd correction. No additional feature or history was fitted.

This is an explicit forced map of the whole cut tail through B,L. It is not closed under a second cut of31: the new B no longer has the required constant parity, and the newly produced L is not the original zero wall. A recurrence for this enlarged class has not been supplied.

## 6. Positive noncancellation: five fixed forcing ones per short event

The six single forcing positions associated with a short start e are

    2e+{-25,-24,-15,-14,-13,-12}.

Their diameter is13, less than the minimum physical separation16 between short starts, so these six-point sets for distinct events are disjoint. The q=1 correction associated with starts e-8,e occurs at2e-25: it cancels precisely the leading odd forcing bit of the SECOND event. It neither cancels another position nor introduces an extra one elsewhere.

Every short event therefore contributes the five fixed, distinct forcing ones

    2e-24, 2e-15, 2e-14, 2e-13, 2e-12,

plus the sixth at2e-25 exactly when there is no short start at e-8. In particular three fixed pulses are even-time and two are odd-time; the optional pulse is odd. On a one-sided actual gate take sufficiently late events so all these times and local windows lie after the certified onset. Any finite collection of such events supplies at least five times as many distinct L=1 positions.

This is a forcing noncancellation bound. It is NOT a bound on a consumed initial reserve. Fixed columns of a finite evolving left row can generate infinitely many forcing events, so infinitely many L pulses do not by themselves contradict FinSupp(Psi empty). A support-compatible invariant, closed different-class reset, or actual charge estimate is still needed.

## 7. Outcome and limits

The useful result is the exact full forced boundary map and its five/six-pulse law. The natural unforced/constant-parity reset fails, but a larger marked boundary class is now explicit. No support descent is inferred from the carrier shift, no class-closure theorem is asserted, and the fixed controls are not identified with the actual gate. The uniform formula follows from the local language domain, and the existing eight-window theorem supplies that domain for every actual refined-gate window. Its application to the prize still requires the missing finite-left compatibility argument.

No Lean build, native application, external API, broad search, or public modification occurred. The two authorized fixed controls and root's separately owned26-window check are distinguished from the paper locality and noncancellation deductions.

## 8. Exact source interfaces

The checked inverse recurrence is Rule30ZeroBoundary.recon; recon_local and recon_aff give its cone dependence and final-input coefficient. The checked actual gate language is Rule30EmptyGateLanguageResearch.windowWord_allowed, with refinedGate(r)=u empty(155+r). The physical twelve-column forcing convention is documented in physical-gate-event-recoding-20261027T0320/PAPER.md. Root's saved carrier, scalar defect, and full local-function evidence are respectively period5-carrier-defect-20261027T0820/{RESULT.json,DEFECT-RESULT.json,TRANSLATIONS.json} and cut31-local-event-map-20261027T0840/{probe.py,RESULT.json}. SOURCES.json pins the read bytes; it does not promote these paper/scalar files to kernel evidence. The coordinate audit carrier-shift-coordinate-audit-20261027T0830/PAPER.md distinguishes a same-orbit shift from a different-member support reset.
