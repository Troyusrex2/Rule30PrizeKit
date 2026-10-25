"""Verify transfers, safely unpack evidence, and install only exact new owned imports."""
import hashlib,json,zipfile
from pathlib import Path
from core import HERE,BASE
root=HERE/'g913-offload';cache=root/'_cache';record=json.loads((cache/'budget8-verified-transfer.json').read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(cache/'budget8-verified-evidence.zip')==record['evidence_sha256']
assert sha(cache/'budget8-verified-objects.zip')==record['objects_sha256']
def unpack(archive,dest,object_mode=False):
 dest=dest.resolve();dest.mkdir(parents=True,exist_ok=True)
 with zipfile.ZipFile(archive) as z:
  for rec in z.infolist():
   assert not rec.is_dir();target=(dest/rec.filename).resolve();assert target.is_relative_to(dest) and target!=dest
   if object_mode:
    assert '/' not in rec.filename and '\\' not in rec.filename
    module=rec.filename.split('.olean',1)[0]
    assert module=='Rule30GoldenBudget8C600V2Research' or (module.startswith('Rule30GoldenBudget8C600Part') and module.endswith('Research') and module[len('Rule30GoldenBudget8C600Part'):-len('Research')].isdigit()),module
   data=z.read(rec)
   if target.exists():assert target.read_bytes()==data,target.name
   else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
folder=root/'results/budget8-complete';unpack(cache/'budget8-verified-evidence.zip',folder)
d=json.loads((folder/'collection-manifest.json').read_text(encoding='utf-8'))
assert d['certificate_complete'] and not d['full_problem_solved'] and d['leaves']==404
for name,digest in d['files'].items():assert sha(folder/name)==digest,name
# Check object basenames explicitly before copying into this isolated reference checkout.
with zipfile.ZipFile(cache/'budget8-verified-objects.zip') as z:
 assert set(z.namelist())==set(d['object_hashes'])
 for name,digest in d['object_hashes'].items():assert hashlib.sha256(z.read(name)).hexdigest()==digest
unpack(cache/'budget8-verified-objects.zip',BASE/'current-reference-3eca-20261024/.lake/build/lib/lean',True)
print({'transfers_hash_verified':True,'modules':len(d['modules']),'kernel_constants':sum(m['constants'] for m in d['modules']),'new_owned_import_objects':len(d['object_hashes'])},flush=True)
