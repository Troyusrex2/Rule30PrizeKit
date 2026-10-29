# Boundary and observation limits for the clock-drop investigation

The genuine finite-white, all-time period-monotonicity claim is still open. This continuation preserves the two positive results already in PR48 and adds two kernel-checked negative controls against overgeneralizing them. No Prize problem is solved.

## New unbounded statements

Read each integer as an eight-bit cyclic temporal column, least significant bit first. The spatial carrier is the four-word cycle 86,149,101,89. Its adjacent pairs obey delta(new)=older OR previous at every temporal phase. Exit from (86,149) along 154,21,234,170. The final columns 234 and170 have least positive temporal periods eight and two, respectively.

`arbitrary_compatible_period_drop n` repeats that carrier n times, then takes the four-edge exit. It proves a compatible walk of length4n+4 ending at (234,170), together with the two least periods. `cyclic_step_all_time` lifts the finite eight-phase checks to every natural time. The oldest column86 is explicitly nonconstant, so the construction has FREE boundary inputs. It cannot be mistaken for a genuine finite white-boundary orbit. It rules out proving general monotonicity merely by checking any fixed amount of older recurrence-compatible context.

`finite_seed_apparent_drop n` goes further, using the OFFICIAL Rule30FrozenRuler.iter. It constructs an odd initial code, zero above depth4n+4, whose columns4n+3 and4n+4 match those period-eight and period-two templates for every tick t<=2n+1. Thus genuine finite initial configurations can imitate the forbidden drop for arbitrarily long finite windows. This is explicitly a finite observation theorem, NOT an all-time period drop. A two-cells-per-tick interior-agreement lemma transfers the free-boundary strip into the finite code. The infinite templates have proved least periods; the actual finite-code columns are not asserted to have those periods.

An independent literal rule30 truth-table implementation verified67 members of the construction (n=0..64,128,256). It used the separate integer initial-word formula sum(7*16^i,i<n)+5*16^n, and found a later deviation in every tested case. For n256, the guarantee is through tick513 and the first actual deviation is tick686. The first-deviation formula has not been proved or generalized.

## Formal validation

The expanded Rule30EdgeClockDrop module contains99 replayed constants and13 checked headline types, including the previous16 constants/seven headlines. The increase in this continuation is83 constants and six headlines. Fresh five-source Lake build at exact official pin932cf8dde039b89b1dcbe9636867bb1b2057fef0; unchanged checker SHA-256 b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905; canonical proof source SHA-256 4112e11292de2d1cf657c586ee88110319712d70412f4dbf422e51b29e94c58e. Attempt03 passed with no new axioms, no proof-source warnings and no reused objects. No whole-catalog rebuild was performed. Attempt02 passed the kernel check but had deprecated-name and unused-simp warnings; those were fixed and a fresh build/replay passed. The source and unchanged checker are included in the portable package.

## Exact searches and their limits

The fixed-clock white-boundary SAT encoding passed five pre-registered controls: a seed return and nonreturn, a deliberately free-boundary drop, and two no-drop cases covered by the previous complete graphs. Eight targeted genuine white-boundary queries at clocks128,256 and widths24,32,40,48 all returned solver UNKNOWN_INTERRUPT after three seconds. None supports SAT or UNSAT. Their complete cyclic recurrence prevents a repeated finite tail from being mistaken for an orbit return.

One final parent process failed to record its child exit code: it caught psutil.NoSuchProcess before calling Popen.wait, leaving returncode unset. The child had written UNKNOWN_INTERRUPT to both its result and stdout. This is recorded, not treated as a successful process run. The parent was corrected to call wait, and a separate seed-return control passed; the expensive target matrix was not repeated. SAT-DRIVER-NOTE.json records the issue and exact solver binary hash. No SAT claim is used by the Lean proofs.

The full temporal-word context graph is a DIFFERENT relaxation from the white-boundary reachable graph. At clock4 it has112 local drop edges, none with arbitrarily deep older context; at clock8 it has13216 drop edges,16 with arbitrarily deep older context. The latter supplied the carrier/exit discovery. These graph counts are Python results. The specific unbounded family was subsequently proved in Lean.

## What remains useful to pursue

Any proof of the genuine all-time no-drop claim must use the white-boundary ancestry and a full-orbit argument. The already checked immediate post-doubling and constant-column branches survive these controls. Equal-clock plateaus with a nonconstant half-shift defect remain open. The new examples do not imply anything about the special legal gate language or the physical center column.

This continuation uses the remaining part of the SAME four-point allowance (original4% used, absolute8%, mathematical-work cutoff7%). No reset, paid worker, subagent, tool installation, computer configuration change or Prize submission was made. Existing Claude R5-01 receipt is still unconfirmed; a separate update can point it to these new constraints without altering its sealed handoff.
