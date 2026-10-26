# Agent target: an admissible lower-clock mode observer

Prize Problem 1, the unrestricted canonical observer and the fixed-center
bridge remain open. The cubic decoder template is already refuted by the
preceding finite certificate; do not reuse its finite successes as a
uniform premise.

The new [report](REPORT.md) provides a proved finite-head-window decoder
for the clock-extending case and a more precise target for a plateau.
All 41 modules were rebuilt and fully replayed at the new official pin
`5473ffd075f63c9d626e63b8455805d4831b39ca`; checker and statements are
unchanged. There are three new modules, 97 new declarations.

For consecutive actual profiles `g,h,k,l`, suppose `h` is antiperiodic
over `P`, `k` is periodic over `P`, and `g` is periodic over `2P`. Put

```
r   = g OR h,
q   = delta_P g,
rho = delta_P r,
S   = NOT delta_1 rho.
```

Lean proves, for every time,

```
q(t+1) = q(t) XOR NOT k(t),
S(t)   = q(t) OR (NOT k(t) AND NOT l(t)),
q(t+P) = q(t).
```

The cyclic XOR of `S` over `P` equals the parity of `P`. Hence `S` has
even XOR at positive even clocks. Recovering the entire `q` trace would
recover `k` by `k(t)=NOT(q(t+1) XOR q(t))`.

**The candidate question:** when two canonical finite-white realizations
have the same `S` at every time and the same positive clock `P`, must
their initial mode bits agree? Formulate a class with all hypotheses
explicit before attempting a proof. The mode `q` is not asserted to be
`Actual`; the old observer theorem cannot simply be applied to it.

The strongest current experiment additionally constrains every ancestor
column in the white-prefix graph to period `P`. Within that restricted
family, the clock-64 graph has 167,168 canonical plateau rows, with
41,792 distinct observations and 41,792 distinct modes, and no collisions.
This is finite evidence, not a proof. The extra ancestor restriction is
not implied by `k`'s period without another argument. No general
no-period-drop theorem is available.

Useful directions:

- Prove or falsify the admissible-mode observer while retaining its actual
  finite white ancestry. Seek a family closed under repeated clock
  descent, including longer plateau chains.
- Explain the observed mode/readout pairing structurally. The simple
  formula `q=S AND S_prev` fails at clock 16 on parent `100000000`;
  `no101` and a simple mask-image guess fail too. Exact data are included.
- If a mode observer is proved, supply the extension/clock argument
  connecting recovered older profiles to full canonical reconstruction.
  It is not already a complete induction. Fixed sheared-depth separation
  still needs a separate bridge to the physical center column.
- The generic cubic-annihilation transfer is now proved. Finishing the
  preceding finite certificate's remaining generic bridges is useful,
  but should not replace work toward the full prize statement.

Tiny sequential readers were exhaustively falsified. Learned tree and
paired-stream readers did not survive validation; larger searches were
inconclusive. Saved transition tables show genuine state collisions on
valid data, so output relabeling cannot repair those particular programs.

Return multiple responses in distinct versioned directories:
`D:\MWB\Rule30\agent-inbox\<unique_response_id>\`. Include `manifest.json`,
`REPORT.md`, sources and evidence; write an empty `READY` file last.
Use the [multi-finding response format](../../RESPONSE_FORMAT.md).
Do not edit another response, prior archives or the coordinator checkout.
Separate experiments, conjectures and full kernel proofs. Preserve all
hypotheses and supply the exact unchanged-checker report for proof claims.
