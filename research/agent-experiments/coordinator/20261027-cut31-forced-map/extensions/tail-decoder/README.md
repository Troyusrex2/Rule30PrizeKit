# Gate-tail decoder and failure of a proposed spacetime factor

This is an extension of the immutable [cut-31 forcing archive](../../README.md). It adds one exact Lean source and the evidence for a fixed failed follow-up. The parent's 90 payload files, README, and inner manifest remain unchanged. This extension has its own manifest and needs the parent source closure for reproduction.

The new source, [Rule30Cut31TailDecoderResearch.lean](Rule30Cut31TailDecoderResearch.lean), has SHA256 `2b563e10d29840681e3bb33b6780a69a693a753d683ed19db29dc82ffcb8f40b`. It imports the parent's unchanged `Rule30Cut31ForcedMapResearch`. No parent Lean source or checker is duplicated here.

For the actual gate `G(r)=u empty(155+r)`, let `K(r)=G(r) AND G(r+3)`, and retain the parent's observations `B=X32` and `L=X31 AND NOT X32`. The two checked headlines prove, for every natural `r`,

```
M(r) = L(2r) AND L(2r+2) = K(r+7),

G(r+7) = NOT B(2r+12)
         XOR M(r) XOR M(r+4) XOR M(r+6)
         XOR M(r+7) XOR M(r+11).
```

The theorem names are `Ruliology.CellularAutomata.Rule30Cut31TailDecoderResearch.actual_marker_decoder` and `Ruliology.CellularAutomata.Rule30Cut31TailDecoderResearch.actual_gate_tail_decoder`. Their complete types and axiom lists are retained in [evidence/root/Types.log](evidence/root/Types.log).

The marker proof uses the same 26 seventeen-bit words as the parent map. Actual membership is supplied by the parent's theorem at every natural index. The gate proof then cancels the five marker terms symbolically. There is no new trajectory, larger certificate domain, supplied clock, or finite-support hypothesis in the Lean proof.

This recovers the original gate **from index seven onward** using both B and L. It does not recover the first seven samples, establish injectivity for arbitrary gates, or prove a physical restart, spatial-cut closure, support-preserving decoder, or support descent. `CQ01Empty` and Prize Problem 1 remain open.

## A recovered boundary does not establish a physical factor

The separate fixed experiment tested one fully specified zero-preserving spacetime code, at two prescribed histories and one fixed stencil window. Its definition and bounds are retained in [factor-control/PROTOCOL.md](factor-control/PROTOCOL.md), with exact [results](factor-control/RESULT.json), [cones](factor-control/CONES.json), and [report](factor-control/REPORT.md). These are scalar evidence, not Lean theorems.

On the actual empty-driven gate, the candidate rows at times 0,1,2, in order `Y0,Y1,Y2,Y3`, are

```
[1,0,1,1]
[1,1,1,1]
[0,1,1,1]
```

The candidate recovers the expected boundary but violates the interior Rule 30 stencil:

```
Y2(1) = 1,
rule(Y3(0),Y2(0),Y1(0)) = 1 XOR (1 OR 0) = 0.
```

The wall `Y0` does not enter this failure. Replacing or masking that wall cannot fix it. An independent scalar review reconstructed only these four decisive values from the retained actual gate with the literal eight-entry Rule 30 truth table. Its required boundary times stop at 58, inside the original 64-bit cone. See [audit/AUDIT.md](audit/AUDIT.md) and [audit/RESULT.json](audit/RESULT.json).

This rejects the specified factor, not the proved gate-tail decoder or every possible code. The relevant actual history is the reconstructed zero-boundary left history associated with the empty-driven right gate. Finite support of its left row is not asserted, and it is not identified with the single-seed center orbit.

## Completed validation versus available reproduction

Two stages of validation have actually completed:

1. The unchanged parent archive has a fresh **21-source** Lake build and full checker replay of three selected modules: **401 constants / 10 headlines**.
2. This decoder was freshly compiled and fully replayed by both its author and an independent root run: **9 constants / 2 headlines**, each using **21 hash-checked existing dependencies**. The root used the objects from the parent's fresh build. Its checker JSON equals the author's exactly, and its types/axioms transcript is byte-identical. The root guard recorded 2.089 seconds, peak owned memory 790,884,352 bytes, and no stop. There were no source-build warnings or new axioms. Both headlines use only `propext` and `Quot.sound`.

The root receipts are in [evidence/root](evidence/root). The author receipts are retained separately in [evidence/author](evidence/author). Nine constants include generated/internal constants; seven are noninternal declared constants. The historical independent audit preceded the root replay; the later root receipts supply that additional validation without changing the audit.

**A combined fresh 22-source build and 410/12 replay has not been performed for this extension.** The script below provides that reproduction procedure. The recorded two-stage evidence is not relabeled as a completed fresh 22-source run.

The exact official pin remains `7d665044b904117af9e82328aeb90a30692b2b85`, with Lean 4.35.0 and the unchanged parent checker SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. There is no Mathlib dependency.

## Reproduction

Keep this directory at `extensions/tail-decoder` beneath the parent archive. From the parent archive root:

```
python extensions/tail-decoder/verify.py --audit-only
python extensions/tail-decoder/verify.py --lean /path/to/lean --lake /path/to/lake
```

On Windows use the matching `lean.exe` and `lake.exe`. The optional `--parent PATH` explicitly selects the parent archive root; its exact manifest and source metadata hashes must still match. The script does not install a toolchain or fetch packages.

`verify.py` reads the parent's 21 exact sources and this one source into a new project, appends only the decoder's `lean_lib` entry to the copied Lake configuration, clears external `LEAN_PATH`, and runs `lake build Rule30Cut31TailDecoderResearch`. It then invokes the unchanged parent checker on its original three modules and this decoder, expecting 410 constants and 12 headlines. It prints all twelve types and axiom lists and compares them with the concatenated parent and decoder transcripts, ignoring whitespace only. It never edits the parent or existing evidence. New outputs go to a unique `runs` directory in this extension.

Optional independent scalar reproductions are separate from the Lean build:

```
python extensions/tail-decoder/reproduce_witness.py
python extensions/tail-decoder/reproduce_control.py
```

The first reconstructs only the four decisive values from retained input. The second runs the original fixed two-history script in a new output directory and checks its saved data and parsed cone values, excluding elapsed time and the explicitly normalized protocol hash. Comparing parsed JSON makes the cone check independent of Windows versus Unix line endings. Neither runs as part of `verify.py`. The second is the same bounded experiment, not an expanded search. Use the wrapper rather than running the retained `factor-control/probe.py` in place, so historical evidence is never overwritten.

[PORTABILITY.json](PORTABILITY.json) and [PROVENANCE.json](PROVENANCE.json) record every transformed artifact and its original/portable hashes. Only private workspace prefixes, worker labels, and invocation commands were removed; exact Lean source, mathematical JSON, printed types, scalar data and cone values were retained. Historical protocol hashes refer to the original sealed protocol. Guard files are labeled resource extracts. There are no compiled objects, credentials, account/session/usage records, private launch scripts, or native Wolfram/LeanLink claims in this extension.

Credits: Troy Lowry and OpenAI Codex. This is research evidence, not a prize submission or a claim of human/catalog acceptance.
