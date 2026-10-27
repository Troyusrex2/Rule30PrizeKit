# Independent decoder and fixed-factor audit

PASS, with the scopes below. The reviewed decoder source is `Rule30Cut31TailDecoderResearch.lean`, SHA256 `2b563e10d29840681e3bb33b6780a69a693a753d683ed19db29dc82ffcb8f40b`, in `cut31-tail-decoder-formal-20261027T0900`. The reviewed fixed experiment is `cut31-next-factor-test-20261027T0905`. All 43 decoder-manifest payloads and all 11 experiment-manifest payloads match their hashes and sizes. Their manifest hashes are respectively `121ed5551152d336e3bab3fe4473e61c72dd4df653cc0ddf0f98f9034c8b3be5` and `5fcf488f84a38bc35801290941bdf4950a69879e1d36e6005a333dd855e59892`.

## Exact formal scope

I read the complete decoder source and both printed headline types and axiom lists. Put `G(r)=u empty(155+r)`, `K(r)=G(r) AND G(r+3)`, and use the frozen physical cut observations `B=X32` and `L=X31 AND NOT X32`. The two actual theorems say, for every natural `r`,

```
M(r) = L(2r) AND L(2r+2) = K(r+7),
gateRead(B,L,r) = G(r+7),
```

where `gateRead` is `NOT B(2r+12)` XOR the five markers `M(r),M(r+4),M(r+6),M(r+7),M(r+11)`. Both types have only the natural index as an explicit parameter; neither has a supplied language, period, finite-support, or return premise. Both use only `propext` and `Quot.sound`.

The marker certificate uses the unchanged 26 allowed seventeen-bit words. Its two adjacent even forcing expressions use gate bits through index 16, so its finite domain suffices. The inherited `actual_seventeen` theorem supplies membership at every natural index, including zero. The gate decoder then cancels the five marker terms in the even B formula at index `r+6`; the recovered marker offsets are exactly 7,11,13,14,18. There is no new longer-window certificate or hidden membership hypothesis. The greatest forcing observation used is `L(2r+24)`.

This is recovery of the actual gate **tail from index seven onward**, using the full B/L observation. It does not recover the first seven samples, prove injectivity on an arbitrary class of gates, or recover the whole finite initial row. In particular, temporal decoding is not a spatial reset or a map proved to commute with Rule 30. No support preservation, second-cut closure, descending support bound, `CQ01Empty`, or prize conclusion is present.

The author receipt is full kernel PASS: 9 owned constants, of which 7 are noninternal declared constants, and 2 headlines; no new axioms and an empty source-build log. Raw checker JSON equals the report and aggregate receipt. The expected checker deprecation warning is retained. The unchanged checker hash is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`, at official pin `7d665044b904117af9e82328aeb90a30692b2b85`.

All 21 dependency source copies match the prior independently fresh-built project. Their recorded object hashes match the preceding successful receipts and this author's reuse record. The complete 22-source closure and import/build order match the literal imports and contain no cycle or omitted dependency. I did not independently rehash remote compiled objects or rerun Lean. This is an independent source/type/provenance audit of the author's 9/2 result; a new root replay is not claimed here.

## Literal fixed-factor failure

I read the frozen protocol and executed script, verified their recorded hashes, and reviewed the saved cones and scalar controls. Official `white`, `packed_white`, `white_sound`, and `white_gate` fix the convention: `W0=1`, `W(q+1)=step_true(step_false(Wq))`, and bit zero of `Wq` is `u empty q`. Thus index 155 corresponds to physical white time 311. The script's empty right-half evolution applies the alternating boundary at the pre-update time and compares complete odd-time rows, not sheared triangular rows. Its recorded comparison through time 373 is author evidence, not a new trajectory run by this reviewer. I also checked all 31 adjacent transitions among the saved 32 packed rows and their sampled low bits.

The fixed candidate defines `B_j=X(j+31)`, `L_j=X(j+30) AND NOT X(j+31)`, and uses the stated distinct even/odd temporal formulas. In particular `j=1` is the proved B/L interface. Its even formula is the complement of `gateRead`; the odd formula has the six markers and quadratic term needed to cancel the odd B formula. Boundary recovery alone imposes no recurrence on the interior `j>=2` outputs.

I independently recomputed only the decisive four values for the actual saved gate, using the literal eight-entry physical Rule 30 truth table to solve each inverse cell. This required 1,363 inverse cells, depth at most 34, and boundary times at most 58, all inside the existing 64-bit cone. Every visited cell matches the saved cone; no boundary wrapping, extra time horizon, carrier trajectory, or further parameter was used. The computation took approximately 0.0026 seconds.

The verified values are

```
Y1(0)=0,  Y2(0)=1,  Y3(0)=1,  Y2(1)=1.
```

With spatial depth increasing to the physical left, the required interior stencil is

```
Y2(1) = rule(Y3(0),Y2(0),Y1(0))
      = 1 XOR (1 OR 0) = 0.
```

Its left side is 1. The wall `Y0` is absent, so changing or masking that wall cannot repair this failure. The complete saved rows are `[1,0,1,1]`, `[1,1,1,1]`, and `[0,1,1,1]` at times 0,1,2; the decisive interior failure agrees with them. The experiment's larger fixed evaluation uses boundary input only through time 59, still within the supplied cone.

This refutes the **specified** zero-preserving spacetime factor on the reconstructed zero-boundary left history associated with the actual empty-driven gate. It does not refute the already proved gate-tail decoder or every alternative code. Finite support of the reconstructed left row is not assumed or demonstrated, and this is not the actual single-seed center orbit. The failure remains exact scalar evidence, not a Lean theorem. No reviewer build, new forward trajectory, enlarged search, publication, or source edit occurred.
