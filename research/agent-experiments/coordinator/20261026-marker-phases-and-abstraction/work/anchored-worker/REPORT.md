# Genuine-seed saturation of a pointwise half-clock abstraction

`AnchoredDefectAbstraction.lean` passed full unchanged-checker replay:59 declarations. It proves that the precise small abstraction described below cannot separate the previously certified mixed strip from a genuine first clock-birth seed. It does NOT prove that any abstract path is an actual temporal trajectory, that the mixed strip has finite-white ancestry, or that all richer invariants fail.

## Genuine seed, not a freely supplied strip

The seed comes from the already-known fixed genuine word11011001001. Its first prefix failing whole-word return16 is

    older = 110110010
    birth = 1101100100.

The kernel checks literal finite-white evolution: older returns16; birth evolves after16 to older++[true], returns32, and every strictly shorter prefix of birth returns16. It also proves, for all natural times, that the older newest trace is16-periodic and the newborn newest trace is anti16. Thus the older defect is identically0 and the newborn defect identically1. These are whole-prefix and actual-history statements, not inferred from a free profile.

## Exact abstract domain and transition

For two adjacent traces A,u at time t, the state records their eight Boolean values at

    t, t+1, t+16, t+17.

The state is a code in Fin256; time parity is retained separately in Fin2. The two half-clock defects and the signed one-step white-height increments at the sampled phases are functions of these bits and parity. Consequently any predicate or inequality built only from those quantities is a predicate on this domain.

`valid` imposes the adjacent transition-cover inequalities at both sampled edges:

    u <= D A <= u OR u_next.

There are100 such states, computed by the finite Boolean analysis. The kernel theorem quantifies over every state satisfying `valid`, rather than assuming that count.

An abstract extension chooses b(t) and b(t+16) independently, then computes b(t+1) and b(t+17) using the exact Rule30 XOR/OR equations. The older part of the new pair is A. `actual_extension_observed` proves that observing any actual extension yields one of these abstract transitions; `cover_preserved` proves cover validity is preserved. This is a sound overapproximation of actual extensions, with deliberately forgotten information.

The forgotten information includes the compatibility of b(t) and b(t+16) through the intervening16 updates, the common choices needed at other observation times, accumulated heights, and temporal phase beyond parity. No full-prefix clock is carried by this abstract state after a transition. A closure theorem for this transition is stronger than closure under only the globally realizable transitions.

## Kernel-verified saturation result

The seed table has10 even-phase observations and4 odd-phase observations, all explicitly certified as observations of the same actual birth word at their stated times. No seed entry comes from the mixed control.

A finite rank/predecessor certificate proves that every cover-admissible state is reachable in at most4 abstract steps from one of those genuine observations, for each parity. The generic `invariant_saturation` theorem is proved by strong induction on the certified rank. Its stronger genuine-seed form says:

If a predicate I on parity and state holds at every actual observation of this genuine birth, and I is closed under every transition of this abstraction, then I holds at every cover-admissible state.

`mixed_control_not_separated` applies this to every sampled A/u and b/A pair of the frozen mixed strip, at each t in Fin32. Therefore no predicate closed under THIS overapproximate transition can reject even one of those observations while accepting the genuine seed. Different observation times can use DIFFERENT abstract paths. The theorem never assembles them into one global spatial extension history.

This is a precise insufficiency result for the selected domain. It does not say that a predicate over richer state, a predicate tracking accumulated or half-interval heights, or an exact transition relation restricted by full temporal histories cannot work. It also does not establish closure when the forbidden cylinders are imposed as global temporal conditions: those longer contiguous windows are not represented in this domain.

## The exact correlation lost

For an actual child b driven by A OR u,

    b(t+16) XOR b(t)
      = XOR over r=t,...,t+15 of (A(r) OR u(r)).

The abstraction retains only the two sampled edges, so it permits both values of the left side independently of that interval parity. The earlier half-clock defect recurrence likewise contains products of a defect with the OTHER parent's original or shifted value. A successful refinement must preserve enough of these interval/correlation constraints to restrict transitions, or use a different invariant. This task did not automatically enlarge the time window, sweep abstract domains, or assert that one extra statistic is sufficient.

## Validation and exact identities

Final source SHA-256: `b3668ec09138e22bb3f0139ecc711833750c19882ea51bbfbdb6bdd7edc08bdf`.

Dependency manifest SHA-256: `a6d05a4960b6b7d81e2bf0318c7bf352b9ec6934986076a9acc3ac974ed33652`. Twelve exact dependencies were freshly compiled and fully replayed in this owned phase,611 existing declarations. No peer binaries were used. The frozen mixed-control dependency remains SHA975f1d613efc0e5763dfbcdda326b22ba0fe0626ab0497b3fb1edc08f53689a8.

Official pin5473ffd075f63c9d626e63b8455805d4831b39ca, Lean4.35.0, unchanged checker SHA-256 b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905. No sorry, new axiom, native decision procedure, checker change, or read-only reference change.

The main source passed on attempt01:12.92seconds,2.04GiB peak owned RSS, more than42GiB system memory available. Fresh dependencies took44.57seconds and approximately1.29GiB. All jobs used300-second,8-GiB owned process-tree,2-GiB system-free guards; none fired. Exact source bytes, build/check logs, parsed reports, and guards are preserved under formal/ and evidence/.

The finite abstract analysis used only256 Boolean state codes per parity and four abstract choices, from the one fixed genuine seed. It is not a width/clock census or a new strip search. The first successful run recorded witness paths; the second recorded the same closure plus rank/predecessor tables for certification. Both executions were below0.2seconds/12MiB. No solver was invoked. `input-mixed-strip.json` is an exact copied input with SHAffac62754060e677233413fb617df244282b68e2d7b4984ffa056111fb9d6839; the script now refers to that included copy for reproducibility. This path-only change does not change the generated tables or final Lean bytes.

For an independent fresh replay, copy all `.lean` sources, dependencies.json, guard.py, and replay.py into a fresh owned G913 research folder without lib/formal outputs, then run:

```powershell
C:/Users/troyu/Miniconda3/python.exe <fresh>/guard.py replay.py dependencies
C:/Users/troyu/Miniconda3/python.exe <fresh>/guard.py replay.py AnchoredDefectAbstraction fresh
```

The source generator uses abstract-closure.json and AnchoredDefect.template.lean. The kernel checks the generated certificate; it does not trust the Python reachability calculation. The template and generator are included separately from the exact final source. All jobs are terminal. No publication or prize submission was made by this worker.
