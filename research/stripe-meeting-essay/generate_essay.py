"""Create a self-contained review essay from the checked catalog contribution.

This prepares artifacts only; it never calls the prize submission API.
"""
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CATALOG = '77cd79f5439b3fa05a5d4725e4595aec69937ec3'
REFERENCE = '2f63afda261888e04ec57237290e723190914a1d'
NS = 'Ruliology.CellularAutomata.Rule30StripeMeeting'
HEADS = ['Rule30Submission.stripe_related_same_trace',
         'Rule30Submission.stripe_meeting_is_early',
         'Rule30Submission.stripe_related_preserves_two']

def source(path):
    return subprocess.check_output(['git','show',CATALOG+':'+path],cwd=ROOT)

def adapt(raw):
    text = raw.decode('utf-8').removeprefix('module\n')
    text = text.replace('@[expose] public section','')
    text = '\n'.join(line for line in text.splitlines()
                     if not line.startswith(('public import ','import '))).strip()+'\n'
    return text.replace(NS,'Rule30Submission')

def main():
    paths = ['lean/Ruliology/CellularAutomata/Rule30Certificates/StripeMeeting.lean',
             'lean/Ruliology/CellularAutomata/Rule30StripeMeeting.lean']
    sources = [source(p) for p in paths]
    standalone = 'import Ruliology.CellularAutomata.Rule30Prize\n\n'+'\n'.join(map(adapt,sources))
    (HERE/'Rule30StripeMeetingStandalone.lean').write_text(standalone,encoding='utf-8',newline='\n')
    embedded = standalone
    abstract = ('For arbitrary finite integer rows a,b and center index c, a common stripe-prefix '
        'cut preserves the entire Rule 30 center trace (Rule30Submission.stripe_related_same_trace). '
        'A stripe prefix, read from low bits to high bits, belongs to 0*(1|11)(01)*; the cut j is '
        'at most c, bit j+1 is white in both rows, and all higher bits agree. The relation is '
        'preserved after two steps, though one-step preservation fails. If the rows become '
        'stripe-related at any finite time t while their center observations agree at every '
        'earlier time, they were already related at time zero or one (stripe_meeting_is_early). '
        'Row size, center index and time are unbounded. A 2321-state paired-row certificate '
        'is connected to arbitrary word lengths, exact integer updates, packing, common-cut '
        'semantics and the inductive stripe grammar. This supplies a proved source of infinite '
        'trace ambiguity and eliminates delayed first entry as a separate mechanism. The '
        'comparison kit contains trace-ambiguity examples and the open EdgeObservable '
        'reduction; this result gives an all-size sufficient relation and an all-time entry '
        'constraint. Completeness for equal infinite traces and equivalence with a numerical '
        'normalizer remain open. No prize problem is solved.')
    text = r'''---
Template: ComputationalEssay
Name: Stripe-related Rule 30 rows share their entire center trace
Author: Troy Lowry; OpenAI Codex
Date: 2026-10-24
Description: All-size trace preservation and no delayed first stripe meeting
Abstract: __ABSTRACT__
Keywords: [Rule 30, finite configurations, center trace, Lean, partial result]
ContextPath: ["Wolfram`LeanLink`"]
---

## The result

Work with any finite integer rows a,b and any center index c. The moving
integer update is

    Phi(a) = a XOR ((a << 1) OR (a << 2)).

Bit zero is physically on the right. Initially bit i represents position
c-i; at time t the center is bit c+t. The proof includes the exact local
Rule 30 identity, with the white boundary below bit zero.

Read a prefix from low bits to high bits. Call it a stripe word if it belongs
to `0*(1|11)(01)*`. Two rows are stripe-related if they are equal, or share
a cut j <= c such that both prefixes through j are stripe words ending
black, both bits j+1 are white, and every higher bit agrees.

The first theorem, `stripe_related_same_trace`, says that related rows have
the same center observation at every time. The second,
`stripe_meeting_is_early`, says: if the relation holds at time t and all
preceding center observations agree, then it held at time zero or one.
The third, `stripe_related_preserves_two`, gives preservation after two steps.
All row sizes, center indices and finite times are quantified without bounds.

The converse is open. Equal infinite traces have not been proved to enter
this relation. The theorem does not establish EdgeObservable or solve any
Rule 30 Prize problem.

```wl
ArrayPlot[CellularAutomaton[30,{{1},0},{48,{-48,48}}],Frame->True,
  PlotLabel->"Rule 30 from a single black cell",ImageSize->550]
```

## What was explored

The investigation asks how distinct finite configurations can have equal
center traces. A terminal stripe can be replaced by its highest black cell
when a white separator follows it. The computational relation suggested by
this replacement became the precise common-cut definition above.

The first conjecture, preservation after one step, was false. Rows 2 and 3
at center index 1 are related; their next rows 14 and 13 are not; after two
steps the relation holds again. The successful argument allows that phase
change. A second certificate proves preservation after two steps, and an
induction proves equality of the entire center trace.

The image below uses built-in Rule 30 for rows 2 and 3. Black marks a
difference. The red line marks the observed center, which stays equal.
The finite picture illustrates the all-time theorem; it does not prove it.

```wl
exampleT=48;exampleC=1;exampleMargin=60;
bitAt[a_,i_]:=If[i<0,0,BitAnd[BitShiftRight[a,i],1]];
exampleInitial[a_]:=Table[bitAt[a,exampleC-x],{x,-exampleMargin,exampleMargin}];
exampleA=CellularAutomaton[30,exampleInitial[2],exampleT];
exampleB=CellularAutomaton[30,exampleInitial[3],exampleT];
exampleDifference=MapThread[BitXor,{exampleA,exampleB},2];
exampleCrop=exampleDifference[[All,exampleMargin+1+Range[-24,24]]];
ArrayPlot[exampleCrop,Frame->True,ImageSize->550,
  PlotLabel->Style["Different initial rows\nThe observed center stays equal",14],
  Epilog->{Red,Thick,Line[{{24.5,0},{24.5,49}}]}]
```

The other direction uses a certificate excluding a first meeting at step
two under two equal center observations. Strong induction then excludes a
first meeting at any later finite time. This does not assert that a pair
with equal infinite traces ever meets the relation at all.

## Independent built-in Rule 30 controls

These eight computations compare the packed update with built-in Rule 30
through every cell of each finite row's causal cone. Large white margins
prevent wraparound from entering those cones. Five pairs illustrate trace
preservation. The other three eventually separate; rows 33 and 45 first
separate at time 58 despite both initially fitting in six bits.
These are finite coordinate and instrument checks, separate from the proof.

```wl
ClearAll[stripeRule30Controls];
stripeRule30Controls[]:=Module[{phi,bit,data,cases},
  phi[a_]:=BitXor[a,BitOr[BitShiftLeft[a,1],BitShiftLeft[a,2]]];
  bit[a_,i_]:=If[i<0,0,BitAnd[BitShiftRight[a,i],1]];
  data={{2,3,1,48,True},{10,11,3,48,True},{42,43,6,48,True},
    {84,86,8,48,True},{160,176,7,48,True},{17,25,4,40,False},
    {33,45,5,72,False},{49,48,3,40,False}};
  cases=Table[Module[{a=d[[1]],b=d[[2]],c=d[[3]],h=d[[4]],expected=d[[5]],
      n,margin,initial,ca,rows,cells=0,ok,equal,first},
    n=Max[IntegerLength[a,2],IntegerLength[b,2]];
    margin=c+n+2*h+8;
    initial[word_]:=Table[bit[word,c-x],{x,-margin,margin}];
    ca=CellularAutomaton[30,initial[#],h]& /@ {a,b};
    rows=NestList[phi,#,h]& /@ {a,b};
    ok=And@@Flatten@Table[cells++;
      bit[rows[[r,t+1]],i]==ca[[r,t+1,margin+1+c+t-i]],
      {r,1,2},{t,0,h},{i,0,n+2*t}];
    equal=And@@Table[ca[[1,t+1,margin+1]]==ca[[2,t+1,margin+1]],{t,0,h}];
    first=SelectFirst[Range[0,h],ca[[1,#+1,margin+1]]!=ca[[2,#+1,margin+1]]&,
      Missing["NoDifferenceInFiniteRange"]];
    <|"Rows"->{a,b},"CenterIndex"->c,"ThroughTime"->h,
      "BuiltinPackedRowMatches"->ok,"ScalarCellsCompared"->cells,
      "TraceExpectationMatches"->(equal===expected),"FirstDifferenceTime"->first|>
  ],{d,data}];
  <|"FiniteControlsOnly"->True,"BuiltinRule30Pairs"->Length[cases],
    "ScalarCellsCompared"->Total[Lookup[cases,"ScalarCellsCompared"]],
    "Cases"->cases,"AllPassed"->And@@Flatten[Lookup[cases,
      {"BuiltinPackedRowMatches","TraceExpectationMatches"}]]|>
];
stripeRule30Controls[]
```

## Why the certificate has unbounded scope

The paired-row transducer reads arbitrary-length bit words. It remembers
four preceding bits per input row, the center marker, and three common-cut
parsers for the rows at times zero, one and two. The 2321-state balanced tree
certifies initial membership, closure under every accepted symbol, exclusion
of the forbidden first-meeting pattern, and two-step preservation.

The finite certificate alone would not prove a statement about arbitrary
rows. The companion proofs establish exact packed-field decoding and bounds,
the two integer output layers, acceptance of actual inputs under the center
guards, and parser semantics in terms of a common cut. Five zero input bits
are explicitly related to actual row continuations. Arbitrarily large zero
bounds turn prefix equality into whole-row equality. Both directions of the
stripe-language interpretation are proved. Finally the two inductions give
all-time trace preservation and the early-meeting theorem.

## The formal proof

The notebook carries the complete proof source from catalog PR 13 at commit
77cd79f5439b3fa05a5d4725e4595aec69937ec3. Only module/import/export wrappers,
module boundaries and namespace qualification change. The source is embedded
as a string; it imports no unmerged module and reads no local proof file.
The kit is obtained from the verifier's environment variable.

```wl
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit=Environment["RULE30PRIZE_KIT"];
```

```wl
rule30Submission=LeanImportString[__LEAN_SOURCE__,"ProjectDir"->$Rule30PrizeKit]
```

## Full kernel replay and theorem statements

The first check replays every declaration of the embedded module. The axiom
lists are shown in addition to that replay. The statements printed below
are Lean's own theorem types, including their exact premises and quantifiers.

```wl
rule30KernelCheck=rule30Submission["Rule30Submission.stripe_related_same_trace"]["KernelCheck"];
{rule30KernelCheck,Association@Table[name-><|
  "Statement"->rule30Submission[name]["TypeForm"],
  "Axioms"->rule30Submission[name]["Axioms"]|>,
  {name,{"Rule30Submission.stripe_related_same_trace",
    "Rule30Submission.stripe_meeting_is_early",
    "Rule30Submission.stripe_related_preserves_two"}}]}
```

The essential semantic bridges identify the tail grammar, the run of the
actual integer bit stream, and the parser's whole-row relation. Their types
make explicit what connects the finite certificate to the final theorem.

```wl
Association@Table[name->rule30Submission[name]["TypeForm"],
 {name,{"Rule30Submission.tailRun_accept_iff",
   "Rule30Submission.actualInput_run","Rule30Submission.relationRun_full_iff"}}]
```

## What remains open

Equal infinite center traces have not been proved to imply stripe relation
at time zero or one. The absence of delayed first meetings cannot supply
that missing existence statement. The relation is proved sufficient for
trace equality; it has not been proved necessary.

The historical numerical normalizer agrees with this relation in finite
controls, but their equivalence has not been formalized. No fixed finite
recovery horizon is claimed. Distinct rows can agree for long finite times.
The full prize question concerns every possible eventual period and
transient of the seed's center column; this essay excludes none of them.

The comparison kit already has finite trace-ambiguity examples and the open
EdgeObservable reduction to Problem 1. This contribution adds a precise
all-size relation with whole-trace preservation, two-step stability and an
all-time entry constraint. It supplies reusable catalog theorems, rather
than another bounded period or word exclusion.

## References and provenance

- [Catalog PR 13](https://github.com/WolframInstitute/Rule30PrizeKit/pull/13),
  with the two core-Lean modules and catalog registration.
- [Research source and independent checks](https://github.com/Troyusrex2/Rule30PrizeKit/tree/b7c1abb/research/normalization-first-meeting).
- [Reference kit at 2f63afda261888e04ec57237290e723190914a1d](https://github.com/WolframInstitute/Rule30PrizeKit/tree/2f63afda261888e04ec57237290e723190914a1d),
  including Rule30TraceEdge, Rule30TraceMerge and Rule30TraceAmbiguity.
- [Wolfram CellularAutomaton documentation](https://reference.wolfram.com/language/ref/CellularAutomaton.html).
- [Rule 30 Prize rules](https://rule30prize.org/).

Research and formalization by OpenAI Codex, working with Troy Lowry.
No historical-priority claim is made. This notebook is a partial-result
review artifact; generation of the notebook does not submit it to the prize API.
'''
    text = text.replace('__ABSTRACT__',abstract).replace('__LEAN_SOURCE__',json.dumps(embedded,ensure_ascii=False))
    (HERE/'stripe-meeting-essay.md').write_text(text,encoding='utf-8',newline='\n')
    (HERE/'notebook-config.json').write_text(json.dumps({'SourceFile':'Rule30StripeMeetingStandalone.lean',
        'EssayFile':'stripe-meeting-essay.md','Headlines':HEADS},indent=2)+'\n',encoding='utf-8',newline='\n')
    manifest = {'reference_commit':REFERENCE,'catalog_commit':CATALOG,
                'source_modules':[{'path':p,'sha256':hashlib.sha256(raw).hexdigest()}
                                  for p,raw in zip(paths,sources)],
                'standalone_body_sha256':hashlib.sha256(standalone.encode()).hexdigest(),
                'embedded_source_sha256':hashlib.sha256(embedded.encode()).hexdigest(),
                'headlines':HEADS,'full_problem_claim':False,'prize_api_submitted':False}
    (HERE/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'source_lines':len(standalone.splitlines()),'source_bytes':len(embedded.encode()),
                      'headlines':HEADS,'prize_api_submitted':False}))

if __name__=='__main__':
    main()
