"""Read-only provenance for the exact reference and toolchain used."""
from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
ref=owner/'research/verifier9-20261026/project'
version=subprocess.check_output([str(owner/'_cache/payload/toolchain/bin/lean.exe'),'--version'],text=True).strip()
checker=ref/'Check.lean';sha=hashlib.sha256(checker.read_bytes()).hexdigest()
assert sha=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert '4.35.0' in version
(root/'Check.lean').write_bytes(checker.read_bytes())
manifest=json.loads((ref/'lean/lake-manifest.json').read_bytes()) if (ref/'lean/lake-manifest.json').exists() else None
data={'lean_version':version,'checker_sha256':sha,'reference':str(ref),'reference_write':False,'lake_manifest':manifest}
(root/'environment.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'lean_version':version,'checker_sha256':sha}))
