"""Package the checked proof bodies as two core-Lean catalog modules.

Only import/export wrappers, namespace qualification, and module boundaries
change. The second finite certificate moves next to the first certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
OLD = 'Rule30NormalizationMachineResearch'
NEW = 'Ruliology.CellularAutomata.Rule30StripeMeeting'

def body(name):
    source = (HERE/(name+'.lean')).read_text(encoding='utf-8')
    prefix,content = source.split('\nnamespace '+OLD+'\n',1)
    content,suffix = content.rsplit('\nend '+OLD,1)
    assert not suffix.strip()
    return content.strip()+'\n'

def build():
    machine = body('Rule30NormalizationMachineResearch')
    preservation = body('Rule30StripePreservationResearch')
    certificate,rest = preservation.split('theorem StripeRelated.center_pair',1)
    preservation = 'theorem StripeRelated.center_pair'+rest
    cert_header = '''module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Finite certificates for stripe meeting and two-step preservation

A balanced tree of 2321 paired-row transducer states certifies initial
membership, closure under every accepted input, exclusion of a delayed first
stripe meeting, and preservation of an existing stripe relation after two
steps. Rule30StripeMeeting proves the unbounded word and actual-row meanings.
This data module alone is not a theorem about all Rule 30 traces.
-/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Ruliology.CellularAutomata.Rule30StripeMeeting

'''
    main_header = '''module

public import Ruliology.CellularAutomata.Rule30Certificates.StripeMeeting

/-!
# Stripe relations and first meetings of finite Rule 30 rows

In the moving integer frame Phi(a)=a XOR((a<<1) OR(a<<2)), the center is
bit c+t at time t. Two rows are stripe-related if they are equal or share a
cut j<=c, both lower prefixes lie in 0*(1|11)(01)*, bit j+1 is white in both,
and all higher bits agree.

Stripe-related rows have identical entire center traces: the relation is
preserved after two steps, and the first two center observations agree.
Conversely, if rows become stripe-related at any finite time while all
preceding center observations agree, they were related at time zero or one.
All row sizes, center indices and finite times are quantified without bounds.

The proof connects finite certificates to arbitrary input lengths, exact
integer bit updates, typed packing, common-cut parser semantics and the
stripe grammar. It does not prove completeness for equal infinite traces,
numerical-normalizer equivalence, EdgeObservable, or a prize problem.
The component module names in some proof comments refer to the accompanying
research sources, from which these proof bodies are combined unchanged.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30StripeMeeting

'''
    stems = ['MachineSoundness','Window','Packing','Stream','ActualInput',
             'Relation','CommonCut','TailLanguage','FirstMeeting']
    pieces = [body('Rule30Normalization'+stem+'Research') for stem in stems]
    pieces += [preservation,body('Rule30StripeTraceResearch')]
    cert = cert_header+(machine+'\n'+certificate).replace(OLD,NEW)+'\nend '+NEW+'\n'
    main = main_header+'\n'.join(pieces).replace(OLD,NEW)+'\nend '+NEW+'\n'
    return {'Rule30Certificates/StripeMeeting.lean':cert,'Rule30StripeMeeting.lean':main}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,required=True)
    args = parser.parse_args()
    records = []
    for rel,source in build().items():
        path = args.project/'lean/Ruliology/CellularAutomata'/rel
        path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists() and path.read_text(encoding='utf-8') != source:
            raise RuntimeError('Different catalog source exists; inspect it first: '+str(path))
        path.write_text(source,encoding='utf-8',newline='\n')
        records.append({'path':path.relative_to(args.project).as_posix(),
                        'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    print(json.dumps({'catalog_sources':records,'proof_body_changes':'namespace qualification and module boundaries only'}))

if __name__=='__main__':
    main()
