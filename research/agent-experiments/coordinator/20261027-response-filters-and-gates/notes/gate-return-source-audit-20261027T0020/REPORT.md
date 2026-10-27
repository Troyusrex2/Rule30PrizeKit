# Independent source/type scope audit: gated return

Verdict: PASS. No semantic or quantifier defect found in the complete source
`Rule30CAGateReturnResearch.lean`, SHA256
`5c7307c33d2f3875fb668fee4e74d788521b0fedef04e6fb32ea1ed4398c6b17`,
from `../gate-return-formal-root-20261027T0015`.

This is an independent source/scope review, not a duplicate build. Root's
saved unchanged-checker result reports PASS11 constants, three accepted
headlines, and no new axioms. The source and direct dependency hashes are
recorded in REVIEW.json.

## Exact theorem

The dynamics are the literal canonical CA action T=C after A on finite
older-first Boolean lists. `giter u g t` is the actual penultimate-bit
evolution, as established by `titer_append_one` and `titer_append_two`.
`outR` is the newest bit after T^t, and `outS` is the newest bit after the
A half-scan of that same state.

The defined premise is exactly

    Gated u g h := for every t,
      outR(u++[g,h],t) = not(giter u g t),
      outS(u++[g,h],t) = true.

For any P:Nat, if u is nonempty, the WHOLE older prefix returns under T^P,
and this all-time gate holds, `gated_return` proves the WHOLE extended word
returns under T^P. It does not supply a clock from the newest trace, assume
a least clock, or require P positive, even, or dyadic. P=0 is correctly
included and gives the trivial zero-step return.

There is no safety premise on u, no assertion that u is gated, and no gate
inheritance hidden in a definition. The theorem does not assert a physical
fixed-center or arbitrary moving-diagonal gate bridge.

## Complete proof review

`not_constant_outputs` derives a contradiction from both older CA outputs
being the same constant Boolean value. It interleaves the two channels using
the existing literal `word0 u = [true,false,false]++u` evolution. That gives
an actual finite-white column beyond an anchored black first column. The
previously checked `no_constant_after_black` excludes either constant value,
not just constant black. The nonempty-tail premise is used honestly in the
odd-time trace bridge. It cannot simply be deleted: the default CA outputs
of the empty tail are both false.

`gated_no_birth` supposes the penultimate displacement over P is true. Whole
return of u makes that displacement equal to the same Boolean birth value
at every time. The two observed demodulated differences then both equal
true, using the explicit gate and the checked Boolean cancellation lemmas.
Masked demodulation consequently forces both older channels to be false
at every time. This contradicts `not_constant_outputs`. The argument does
not rely on a supplied return of the extended word.

`gated_return` then obtains giter(P)=g from false birth. The gate at time0
gives h=not g. The actual list decomposition at timeP preserves the entire
older prefix, identifies the penultimate bit as g, and uses the gate to
identify the last bit as h. The final equality is of complete lists.

The direct dependency statements and literal observation definitions were
read independently. Root's recorded initial elaboration failure is not a
logical premise; this review covers only the exact final source above.

## Strongest immediate consequence without prefix safety

Under the same nonempty u and Gated premise, the three words

    u,  u++[g],  u++[g,h]

have exactly the same set of whole T-return times. The theorem gives the
older-to-longer direction, and `gated_no_birth` plus `titer_append_one` gives
the intermediate return. The converse directions follow from prefix
autonomy: project an actual whole return onto the earlier prefix using the
checked list decompositions and length preservation.

Therefore their least positive whole T periods coincide whenever one is
defined; existence is available for actual finite tails from the already
established finite-state dynamics. More concretely, if the gated extended
word returns at 2P but does not return at P, then the shorter actual u also
returns at 2P and does not return at P. This is a genuine reduction of a
whole-word nonreturn witness. It supplies no gate on that shorter witness,
so the reduction cannot be iterated as a gated induction without an additional
bridge.

The existing `iter_even_odd` adapter also transfers this equality of return
sets to the corresponding literal finite-white words `100u`, `100(u++[g])`,
and `100(u++[g,h])`, with T-time doubled. Odd full-time returns are excluded
by the distinct 100/111 prefix phases. This uses the already checked canonical
word adapter; it does not identify an arbitrary physical or Nat-indexed gate
instance with this canonical premise.

No new Lean source, build, computation, or public action was performed in
this review. The reviewed theorem is useful local clock exclusion, not the
remaining uniform finite-white gate-halving theorem.
