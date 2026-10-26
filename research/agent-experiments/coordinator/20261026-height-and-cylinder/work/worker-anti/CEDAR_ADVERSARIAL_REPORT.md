# Adversarial D3* track: symbolic anti-period lifting and a failed height invariant

Status: paper identities plus exact finite controls; no Lean theorem, no D3* proof, and no finite-white counterexample. All writes are confined to this worker folder. The prior scalar even-gap lemma is used as established background, not counted as a new result.

## A1. Exact anti-period lift

Let P be positive and even. Let a,b be P-periodic Boolean profiles and let c obey c(t+1)=c(t) XOR (a(t) OR b(t)) with c(t+P)=1-c(t). Let d obey d(t+1)=d(t) XOR (b(t) OR c(t)). Then

    (b OR c)(t) XOR (b OR c)(t+P) = 1-b(t),
    parity(sum_{t<2P} (b OR c)(t)) = parity(sum_{t<P} b(t)).

Hence d returns after 2P exactly when b has even weight over P; otherwise d is anti-2P. This is a profile statement; if the older whole prefix already has least period 2P, it determines whether the whole appended prefix retains that clock or doubles it.

If d returns after 2P, h(t)=d(t+P) XOR d(t) is P-periodic and

    h(t+1) XOR h(t) = 1-b(t).

These identities follow directly by pairing phases t and t+P. They retain a latent half-period difference, rather than replacing the profiles by unmarked event counts.

## A2. A general signed-height obstruction

For a Boolean mask v on a P-cycle, define H_v(0)=0 and

    H_v(k)=sum_{0<=t<k} (-1)^t v(t).

Let b be P-periodic and c anti-P, independently of how c was produced. If a following d is all-time Safe, then for v=1-b,

    H_v(P)=0, and max(H_v)-min(H_v) <= 2.

Proof: write Z(t)=[b(t)=c(t)=0]. Anti-periodicity gives the integer identity Z(t)+Z(t+P)=1-b(t). Under Safe d, Z events alternate temporal parity by the scalar zero-pair-gap criterion. Their signed sum on every contiguous interval therefore lies in {-1,0,1}; their signed sum around the full even 2P-cycle is zero. Any base interval and its P-shift project to the corresponding b-zero interval. Because P is even their signs agree, giving interval imbalance at most 2 and full base drift zero. The bound on all interval differences is exactly the displayed height-amplitude bound. This proof also covers Z empty, when b is identically 1.

Consequently either nonzero drift or amplitude at least 3 excludes Safe d. This is a genuine conditional family lemma, not a finite-width inference.

## A3. The F004 first-break application, and its exact limit

The preserved phase-canonical F004 pairs are (5397,6885) and (22359,23205) at P=16, with bit t encoding phase t. Their OR weights are 11 and 13. Thus both next children c are anti-16: there is no same-clock16 continuation at all. The exact phase-rotation-quotient closure requested here consists of these two states, zero same-clock edges, and two clock-doubling exits. Both states have an even zero-pair gap. A phase quotient is exact here because both complementary children would be included; odd-parity exits are recorded, not treated as impossible descendants.

Both b profiles have weight 8 over16. Therefore their next children d return after32. The b-zero signed heights have drift0 and amplitudes3 and4, respectively. A2 excludes Safe d for either initial c or d bit, despite this same-clock step.

The next projection explains why the amplitude obstruction alone does not propagate. Let

    R(t) = [c(t)=d(t)=0] + [c(t+P)=d(t+P)=0].

Since c is anti-P, this sum is Boolean, and with h=Delta_P d,

    R(t) = 1 XOR d(t) XOR (c(t) AND h(t)).

If a further child e were Safe, the same interval argument would force R to have drift0 and amplitude<=2. The eight prescribed two-step lifts of the two F004 seeds, realized by actual normalized nine-cell white words, give:

| F004 class | Canonical seven-cell seed | Four child initials | b-zero height | Projected R height at canonical origin |
|---|---|---|---|---|
| 0 | 1111011 | 00,01,10,11 | drift0, amplitude3 | amplitude2, drift -1,+1,-1,+1 |
| 1 | 1000011 | 00,01,10,11 | drift0, amplitude4 | amplitude3, drift +2,-2,-2,+2 |

Thus class0 is a concrete genuine-ancestry failure of the proposed inherited threshold “amplitude at least3.” Its next projection falls to2. Nonzero drift still excludes a Safe e in these controls, so this is not a D3* counterexample. Amplitudes in the nonzero-drift column are stated at the displayed canonical origin; unlike zero-drift amplitudes, they need not be rotation invariant.

This supports keeping both ordered phase information and half-period differences. It does not establish that the combined drift/amplitude obstruction survives arbitrary later same-clock descendants. Once both last profiles cease to have a constant half-period difference, the projection formula gains the nonlinear term c*h. Renaming the combined obstruction an invariant would be unjustified.

## A4. Direct countercontrols to monotone signed heights

The named genuine white control10000001 has period32 and pair-zero signed-height amplitudes [0,0,16,8,1,4,6,3] in older-first column order. All its event sets from column3 onward are nonempty. In particular6->3 defeats a monotone-height claim along unsafe descendants. Its column5 triple-event mask has8 events but signed-height amplitude1 and drift0, so small event height does not mean the event set is empty.

The named F009 control111101100000 has period64 and pair-zero amplitudes [0,0,32,16,1,9,12,3,6,4,4,5], giving further decreases. The computations use one common literal whole-word clock and preserve the complete orbit and wrap edge. Raw one-cycle heights with nonzero drift depend on the origin and chosen clock; no phase-independent rank is inferred from them.

## Evidence and limits

## A5. Exact cyclic run-colour criterion with two predecessor equations

The following is a paper theorem with exhaustive finite checking of its
construction, not a Lean theorem. It sharpens the free-c height bound by
retaining two local predecessor equations. The ancestors remain arbitrary
periodic profiles, so this is not a finite-white characterization.

For even positive P and a P-periodic Boolean b, the following are equivalent:

1. There exist P-periodic profiles u,a, an anti-P profile c, and a Safe d with

       Delta b = u OR a,
       Delta c = a OR b,
       Delta d = b OR c.

2. The profile b contains both symbols; the signed height of 1-b has drift0
   and amplitude at most2; and either its amplitude is less than2, or at
   least one maximal cyclic zero run of b has odd length.

Here Delta is temporal XOR difference. Necessity of the height bound is A2.
If b is identically0, the first equation forces a=u=0 and c is constant.
If b is identically1, the second forces c to alternate, which returns after
even P. Both contradict anti-P. At every b00 edge, the first equation
forces a=0 and the second makes c constant. Thus each maximal b-zero run
has one c colour, and appears intact exactly once among the pair00 events
over2P. If all those zero runs have even length, an alternating-parity
pair00 event list requires every run to start at the same temporal parity.
When all runs are even, opposite start parities are exactly the case of
height amplitude2: each run returns to the common height at its boundary,
and its interior reaches one level above or below. This proves the extra
necessity condition.

For sufficiency, choose a global minimum or maximum of the zero height at
a cut which is not inside a b00 edge. Such a cut exists under condition2.
Indeed, if neither extreme is at a run boundary, both extrema are strictly
inside zero runs; amplitude at most2 forces every run boundary to be at the
single middle level. Every zero run is then even and both start parities
occur, precisely the excluded case. The mixed-symbol hypothesis provides
run boundaries.

Rotate to that cut. Colour each zero event by the lower height of its
crossed edge, translated to colour0 or1. Within a contiguous zero run,
temporal signs alternate and cross the same height edge back and forth,
so its colour is constant. Each colour's ordered events alternate signs,
are balanced, and begin with the same sign (positive at a minimum,
negative at a maximum), whenever nonempty. Set c at b-zero times to that
colour in the first P phases and to the opposite colour in the second P
phases. Extend c backwards over each run of b=1 by forced alternation.
Because the cut avoids b00, this gives a consistent anti-P profile.
The resulting pair00 list is the concatenation of the two colour lists,
so its signs alternate cyclically; hence a Safe d exists.

Set a=Delta c on b=0 and a=0 on b=1, and set u=Delta b. The constructed c
toggles at b=1 and is constant at b00. Therefore a<=Delta b pointwise,
which proves both predecessor equations. Their profiles are P-periodic.
Rotate all profiles back to the original phase. No recurrence for u or
any finite-white origin was supplied.

Exact test: run_colour_criterion.py checks all340 b profiles for P=2,4,6,8,
independently enumerating every anti-P c and testing the two necessary and
sufficient local compatibility conditions. It finds71 positive profiles;
the explicit construction succeeds for all71. The named control00100111
has zero drift and amplitude2, but both zero runs are even and start at
opposite parities, so it fails the two-predecessor criterion. The positive
control0011 has amplitude1 and constructs correctly. This is a scalar
periodic-input lemma check, not a finite-white width census or a D3*
counterexample.

## Evidence and limits (continued)

- height_controls.py / height_controls.json: named controls and three tiny members of the previously preserved spatial-avoidance family; full literal XOR/OR cycles and wrap checks. No width census.
- clock16_closure.py / clock16_closure.json: one exact phase-canonical same-clock closure from F004, capped at100000 in code but terminating immediately at2 states. No P32 closure followed.
- symbolic_lift_controls.py / symbolic_lift_controls.json: the8 dictated two-step lifts, complete32-row literal cycles and wrap, anti-period, half-difference, and projected-mask identities. No all-time Safe candidate appeared; no counterexample audit is claimed.
- run_colour_criterion.py / run_colour_criterion.json: exact two-predecessor criterion and explicit construction;340 periodic b profiles independently checked against all compatible anti-P c choices,71 positive constructions.

All four jobs finished in under0.3 seconds each and below16MiB process RSS, under the provided60-second/1GiB guards. No long or active jobs remain at this checkpoint. No API calls, installs, Lean builds, external publication, backend changes or shared-reference edits occurred. The team's audit worker independently replayed all eight literal lift controls, verified their minimal periods and identities, and paper-audited A2 successfully; A5 is awaiting independent review. The global D3* ancestry implication remains open.
