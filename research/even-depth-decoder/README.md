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

All 31 new declarations and eight selected headlines passed full kernel
replay at `3eca23c0a9fa6b153313655e6d51835406c2d06e`, with the unchanged
official checker and standard axioms only. The reproducer first freshly
audits all 139 declarations and 17 selected headlines of the exact external
source, credited above, then checks this module. See [the report](report.json).

Independent controls compare the recursive decoder with physical causal
pivots for 64 prescribed words, 2048 free bits, 133120 truth-table cells,
and 3520 prefix-bit comparisons. Only uncontaminated cones are compared.
These are finite implementation controls; the unbounded inverse identities
and the equivalence come from Lean. See [the controls](even-decode-controls.json).

```text
python research/even-depth-decoder/verify.py --project <3eca23c-reference-checkout> --lake <lake> --output <audit-directory>
python research/even-depth-decoder/control_even_decode.py
```

The proof imports the exact audited external module, which the reproducer
downloads and protects against replacement by different bytes. The checker,
statements and guards are unchanged. No prize essay or prize claim is made.
