"""Extract only the independent golden-language block of a verified submission.

The original whole-module local build reached the resource guard. This
small exact block is replayed separately; no whole-module pass is claimed.
"""
import hashlib,json,urllib.request
from core import HERE

record=HERE/'external'/'9d92a2-original-record.json'
if not record.exists():
    entry=next(e for e in json.loads((HERE/'submissions-later.json').read_text(encoding='utf-8'))['entries']
               if e['id']=='R30-20261024-9d92a2')
    record.write_text(json.dumps({k:entry[k] for k in ['id','authors','status','tags','files','page']},indent=2)+'\n',
                      encoding='utf-8',newline='\n')
entry=json.loads(record.read_text(encoding='utf-8'))
assert entry['status']=='Lean Verified' and 'Human Verified' in entry['tags']
original=HERE/'external'/'VillafuerteVerified-9d92a2.lean'
if not original.exists():original.write_bytes(urllib.request.urlopen(entry['files']['lean'],timeout=45).read())
raw=original.read_bytes();expected='57bd19e546495805c816437239133c694a9ef5ed43a1163b3ad6246f7fe9d1cb'
assert hashlib.sha256(raw).hexdigest()==expected
source=raw.decode('utf-8');start=source.index('theorem u_golden (')
stop=source.index('/-- Well-ordering helper:',start);block=source[start:stop]
prefix='''import Ruliology.CellularAutomata.Rule30PeriodTwoSideways

/-! Exact theorem block extracted from R30-20261024-9d92a2, previously Lean
and Human Verified. Original submission authors: see provenance JSON.
The block is reused with attribution, not claimed as new research here. -/

namespace Rule30Submission
open Ruliology.CellularAutomata
open Rule30Jen Rule30Prize Rule30PeriodTwoSideways Rule30ZeroBoundary Rule30PeriodTwoCoupled
open Rule30Ether (drv drv_col0)

'''
out=HERE/'Rule30VerifiedCoupledGoldenExtract.lean'
out.write_text(prefix+block+'\nend Rule30Submission\n',encoding='utf-8',newline='\n')
provenance={'original_id':entry['id'],'original_authors':entry['authors'],
    'recorded_status':entry['status'],'recorded_tags':entry['tags'],
    'original_source_sha256':expected,'block_sha256':hashlib.sha256(block.encode()).hexdigest(),
    'extracted_source_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),
    'source_block_unchanged':True,'whole_module_local_build_passed':False,
    'whole_module_stop_reason':'owned resource guard; no whole-module pass claimed',
    'page':entry['page'],'headlines':['u_golden','u_black_among_five','Psi_free_no00_no11111']}
(HERE/'external'/'9d92a2-extract-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n',encoding='utf-8',newline='\n')
print({'bytes':out.stat().st_size,'authors':entry['authors']},flush=True)
