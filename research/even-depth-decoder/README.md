# Constructive decoding of the even spatial coordinates

2026-10-24, Troy Lowry with OpenAI Codex. **Q01 and Problem 1 remain open.**

This is a small constructive extension of the all-depth reconstruction by
G.P.J.W. Quint and Gemini (Google),
[submission R30-20261024-ad1748](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261024-ad1748).
Their locality and linear-pivot theorems already provide the triangular
structure used here. We make its inverse explicit and state the remaining
finite-support problem using that inverse. No new period is excluded.

For their `skelPair s`, define `evenCode(s)[d]` as the initial cell at depth
`2*d+2`. The [Lean module](Rule30EvenDecodeResearch.lean) defines a causal
decoder by recursion on `d`: set all future free bits to zero, reconstruct
the next even cell from the already decoded prefix, and XOR that predicted
cell with the requested cell. The external linear pivot proves that this
chooses the unique correct free bit.

The proof establishes both inverse identities, bijectivity for arbitrary
infinite sequences, and exact prefix locality. Thus **every** assignment
of the initial even spatial cells has a unique free sequence and a unique
assignment of the initial odd cells. The latter is `oddCode(u)`.

Writing `FiniteBits(u)` for a sequence that is eventually all white, the
remaining question becomes exactly:

```text
Rule30PeriodTwo.Q01
  iff for every u, FiniteBits(u) implies not FiniteBits(oddCode(u)).
```

This equivalence is proved; **neither side is proved true**. The decoder
does not preserve finite support by assumption. Its reconstructed free
sequence need not satisfy the golden restriction, which requires actual
coupling to an alternating center. Finite prefix observations do not
establish eventual tails of these decoded infinite sequences.

All 31 decoder declarations and eight selected headlines passed full kernel
replay at `3eca23c0a9fa6b153313655e6d51835406c2d06e`, with the unchanged
official checker and standard axioms only. The reproducer first freshly
audits all 139 declarations and 17 selected headlines of the exact external
source, credited above, then checks both research modules. The additional
41 sensitivity declarations and five headlines are described below.
See [the report](report.json).

Independent controls compare the recursive decoder with physical causal
pivots for 64 prescribed words, 2048 free bits, 133120 truth-table cells,
and 3520 prefix-bit comparisons. Only uncontaminated cones are compared.
These are finite implementation controls; the unbounded inverse identities
and the equivalence come from Lean. See [the controls](even-decode-controls.json).

## The pivot of the next odd cell

[The sensitivity module](Rule30OddSensitivityResearch.lean) uses only the
official kit. It proves a general identity for the reconstruction `recon`:
change the head entry at `t+k`, keep earlier entries and the next entry
`t+k+1` fixed, and the difference at depth `k+2` is the changed bit times
an explicit coefficient. That coefficient is the XOR of the preceding
anti-diagonal, with a parity correction when `k` is even.

For the constrained rows `Theta(s)`, let `flipAt(s,d)` flip free bit `d`.
The correction vanishes at the relevant odd index, giving the exact formula

```text
Theta(s)[2*d+3] XOR Theta(flipAt(s,d))[2*d+3]
  = diagParity(alt(s), 2*d+1, 0).
```

The right side XORs the cells at depth `2*d+1` and time zero, depth `2*d`
and time one, through depth one and time `2*d`. It depends only on earlier
free bits. In contrast to the unit pivot of the even spatial cell at depth
`2*d+2`, this odd-cell coefficient can be zero. A white odd cell can therefore
force a unique next free bit, leave both choices available, or be impossible
for either choice. This describes the branching that a finite-odd-support
argument must control; it does not prove that such branching must terminate.

All 41 declarations and five selected headlines passed full kernel replay,
with standard axioms and the unchanged official checker at the same pin.
The [Wolfram controls](odd-sensitivity-controls.wls) independently build
physical rows, evolve them with `CellularAutomaton[30]` and a white wall,
and compare 832 penultimate-entry flips with the physical diagonal parity.
They also check 20352 head-realization cells, with 354 zero-sensitivity and
478 unit-sensitivity cases. Only uncontaminated causal cones are used.
See [the control results](odd-sensitivity-controls.json).

```text
python research/even-depth-decoder/verify.py --project <3eca23c-reference-checkout> --lake <lake> --output <audit-directory>
python research/even-depth-decoder/control_even_decode.py
wolframscript -file research/even-depth-decoder/odd-sensitivity-controls.wls
```

The decoder imports the exact audited external module, which the reproducer
downloads and protects against replacement by different bytes. The checker,
statements and guards are unchanged. The sensitivity module uses only the
official kit. No prize essay or prize claim is made.
