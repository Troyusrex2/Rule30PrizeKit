# The specified spacetime factor fails on the actual empty-driven gate

The single frozen experiment completed exactly its two prescribed histories and fixed stencil window. The candidate recovered the expected boundary on both histories but failed the Rule30 update on both, including an interior failure on the actual gate. No larger test or changed candidate was run.

## Decisive actual-history witness

The actual input was G(r)=u empty(155+r), r=0,...,31. Its chronological bits are

    00100001000010000100100001000010

The complete evaluated candidate rows, in the order j=0,1,2,3, were:

| Time | Y0 | Y1 | Y2 | Y3 |
|---|---:|---:|---:|---:|
| 0 | 1 | 0 | 1 | 1 |
| 1 | 1 | 1 | 1 | 1 |
| 2 | 0 | 1 | 1 | 1 |

At positive depth k=2 and time t=0, the required update is

    Y2(1) = Y3(0) XOR (Y2(0) OR Y1(0)).

The actual candidate gives left side 1 and right side `1 XOR (1 OR 0)=0`. This is an interior stencil. Changing or masking the candidate's wall Y0 cannot repair it. At k=2,t=1 there is another interior failure.

For a direct audit of the four decisive values, the saved constituent data give:

- Y1(0): B1(12)=0 and all five selected M1 values are zero, so Y1(0)=0.
- Y2(0): B2(12)=0; among M2 at indices 0,4,6,7,11 only M2(7)=1, so Y2(0)=1.
- Y3(0): B3(12)=1 and all five selected M3 values are zero, so Y3(0)=1.
- Y2(1): B2(13)=1; the six selected marker values are 1,0,0,1,0,0 and the quadratic product is zero, so Y2(1)=1.

The boundary control Y1(t)=a(t+14) passes at all three tested times t=0,1,2. There is additionally a nonzero masked wall seam at time0, Y0(0) AND NOT Y1(0)=1, but the interior failure is independent of that issue.

## Carrier control

For the pure period-five gate, the three candidate rows were `[0,1,0,1]`, `[1,1,1,1]`, `[0,1,0,1]`. Boundary recovery again passed, and the masked wall seam was zero at both tested update times. Nevertheless the k=2,t=0 interior update failed. Thus even the carrier failure cannot be explained solely by a missing wall mask. The actual-history witness above was still computed and retained as required.

## Independent convention checks and exact bounds

The actual right gate was generated with the exact previously verified packed convention W0=1, W(q+1)=step1(step0(Wq)), only through q=186. An independent scalar evolution of the initially empty right half with alternating prescribed center used the literal eight-entry physical Rule30 truth table. All 187 complete odd-time rows through physical time373 matched the packed rows; 69751 scalar right-side stencils were checked. The saved 32 sampled packed rows identify the actual input without relying on the language alone.

For each history, the left reconstruction used exactly64 boundary bits, through spatial depth34. Each inverse cell was obtained by trying the two possible outer-left bits in the literal physical truth table; uniqueness and agreement with the inverse XOR/OR formula were checked. There were 1551 inverse stencils per history. `CONES.json` retains both complete bounded cones. All candidate outputs use X times at most26 and boundary input times at most59. No unspecified future, finite truncation beyond the required cone, or temporal wrapping enters these values.

The frozen protocol SHA256 is `6d01faf55d1932f067fd4bc942836ddde101a725d8253e397f84e1815391c7d2`; the executed script SHA256 is `ac9473557cd0b8a96e809bbde7653839e794c8ac1dcb43ba344bd7bcc8005476`. These hashes were recorded before execution. The remote worker job finished without a guard stop in 0.1137 seconds, with sampled peak owned RSS 10600448 bytes. Its limits were60 seconds,8 GiB owned RSS, and2 GiB minimum system available memory.

## Scope

This is exact finite scalar evidence refuting the SPECIFIED zero-preserving spacetime decoder as a Rule30 factor, including on the actual empty-driven trace. It does not refute the already kernel-proved boundary decoder, whose output was checked successfully. The actual left history is the reconstruction of the genuine empty-driven gate; no claim that its initial left row is finite is made.

No universal obstruction to other codes, conditional finite-support statement, CQ01Empty counterexample, or prize conclusion follows. No Lean build, new history, larger window, parameter sweep, native application, or public write occurred. All prior sealed sources and proofs remain unchanged.
