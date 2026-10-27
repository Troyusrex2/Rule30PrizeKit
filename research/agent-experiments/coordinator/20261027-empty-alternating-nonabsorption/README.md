# Empty-right alternating nonabsorption

This portable core-Lean project proves that the empty right half, driven by
the alternating boundary, never enters any compatible member of the official
seven-column ether-and-wall family. Consequently
`Rule30Ether.Absorption [true,false,true,false] A` is false for every list
`A` of genuine alignments of that word.

The literal four-slot word matters: the official `wordAt` takes time modulo4,
so a two-entry list `[true,false]` would denote1000. The readout
`u r = drv altCol empty (2*r+1) 1` samples physical site1 every two steps.
Its certified spacing forbids eventual period two. An aligned ether-wall
entry would force physical period four, hence that forbidden readout period.
See [the proof](papers/PROOF.md).

This is an unbounded exclusion of a specified absorption family, not a
Rule30 Prize solution. Arbitrary eventual periodicity of the readout,
`CQ01Empty`, and the separate named period-four absorption instances for
0001,0011,0111 remain open.

## Reproduce

Use Lean4.35.0/Lake and Python3.9 or newer. From this directory run:

```text
python verify.py
```

The script verifies every package hash, runs the actual Lake build of both
new modules, fully replays each through the included unchanged official
checker, and compares all16 printed theorem types with `Types.expected.log`.
The complete direct commands are in [CHECK-COMMANDS.txt](CHECK-COMMANDS.txt).
Fresh evidence is written to a new timestamped `verification-output/` folder.
Nothing is installed. No Mathlib, external service, or private library is
needed. For a fresh source build, start with a fresh copy without `.lake/build`;
this payload contains no compiled objects.

## Exact validation

The fresh integration built all18 source modules from a clean core Lake
project:16 official dependencies and two new modules. Both new modules
passed the unchanged full checker:

| Module | Replayed owned constants | Checked headlines |
|---|---:|---:|
| `Rule30Certificates.AlternatingEmptyWall` | 269 | 2 |
| `Rule30EmptyAlternating` | 37 | 14 |

The total is306 constants and16 headlines.
Constants include generated proof internals; these are not counts of
handwritten theorems. `SUMMARY.json` records the noninternal/internal split.
There were zero source warnings and no new axioms. The10 previously printed
headline types agree after namespace replacement and whitespace normalization;
all16 current types are included. Existing certificate data and retained proof
bodies are unchanged apart from the recorded catalog namespace/import changes.

Official source/configuration pin:
`7d665044b904117af9e82328aeb90a30692b2b85`. All16 official source dependencies also match the
previous5473 pin exactly. The unchanged checker SHA256 is
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

The two exact catalog source hashes are:

* Certificate: `bf9f55d18aa86b8c86a4507c51394074d8857edaaa077a17b7c1621f91b27848`
* Main theorem module: `54ceba337576889c878e04998e2396ca0f83740ffbf3ef5566e2056a24b8de9f`

Raw successful build, full-check, and type logs are included under `receipts/`.
Resource and timing extracts are explicitly labeled and omit machine-specific
process commands; they retain the original receipt hashes. Exact source maps
and the recursive closure are included. Packaging performed no duplicate build.
`MANIFEST.json` maps every distributed relative path to its SHA256, excluding
the manifest itself.
