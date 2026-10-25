"""Read-only validation of the response schema, references and artifact bytes."""
import hashlib,json,sys
from pathlib import Path
from jsonschema import Draft202012Validator,FormatChecker

root=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
manifest=json.loads((root/'manifest.json').read_text(encoding='utf-8'))
schema=json.loads((root/'response_schema.json').read_text(encoding='utf-8'))
Draft202012Validator(schema,format_checker=FormatChecker()).validate(manifest)
assert root.name==manifest['response_id']
ids=[a['artifact_id'] for a in manifest['artifacts']]
assert len(ids)==len(set(ids))
paths=[a['path'] for a in manifest['artifacts']]
assert len(paths)==len(set(paths))
findings=[f['finding_id'] for f in manifest['findings']]
assert len(findings)==len(set(findings))
for artifact in manifest['artifacts']:
    p=(root/artifact['path']).resolve()
    assert p.is_relative_to(root),p
    assert p.is_file(),p
    assert hashlib.sha256(p.read_bytes()).hexdigest()==artifact['sha256'],p
for finding in manifest['findings']:
    assert set(finding['evidence_artifact_ids'])<=set(ids)
    verification=finding['verification']
    if verification['kind']=='full_kernel_replay':
        a=next(a for a in manifest['artifacts'] if a['artifact_id']==verification['checker_report_artifact_id'])
        report=json.loads((root/a['path']).read_text(encoding='utf-8'))
        assert report['kit_commit']==verification['kit_commit']
        assert report['check']['verdict']=='pass' and report['check']['replay']['ok']
        assert report['checker_unchanged'] and not report['check']['newAxioms']
        assert set(verification['headlines'])<=set(report['headlines'])
        assert all(h['ok'] for h in report['check']['headlines'])
        assert report['source_sha256']==hashlib.sha256((root/'CedarAncestry.lean').read_bytes()).hexdigest()
    for ref in finding['depends_on']+finding['conflicts_with']:
        response,local=ref.split('#')
        if response==manifest['response_id']:assert local in findings
actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
assert actual-set(paths)<= {'manifest.json','READY'}, actual-set(paths)
if (root/'READY').exists():assert (root/'READY').stat().st_size==0
print(json.dumps({'valid':True,'response_id':manifest['response_id'],'artifacts':len(ids),
                  'findings':len(findings),'READY':(root/'READY').exists()}))
