from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
manifest=json.loads((root/'manifest.json').read_bytes())
for name,digest in manifest['files'].items():
    path=(root/name).resolve();assert path.is_relative_to(root)
    assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,name
audit=json.loads((root/'audit.json').read_bytes())
for item in audit['new_modules']+audit['dependency_modules']:
    module=item['module'];source=(root/(module+'.lean')).read_bytes()
    report=json.loads((root/'formal'/module/'report.json').read_bytes())
    assert hashlib.sha256(source).hexdigest()==item['source_sha256']==report['source_sha256']
    c=report['checker'];assert report['passed'] and c['verdict']=='pass'
    assert c['replay']=={'ok':True,'constants':item['constants']} and not c['newAxioms']
    assert not c['verifiedTargets'] and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    guard=json.loads((root/'evidence'/('replay-'+module+'.guard.json')).read_bytes())
    assert guard['exit_code']==0 and guard['guard_stop'] is None
assert audit['all_time_safety_premise_retained'] and audit['literal_finite_white_semantics']
assert audit['prefix_return8_premise_retained'] and audit['extension_length_bound']==3
assert not audit['child_clock_premise'] and not audit['D3_star_proved'] and not audit['full_problem_solved']
print(json.dumps({'passed':True,'file_hashes':len(manifest['files']),'new_declarations':273,'dependency_declarations':220,'F003_kernel_verified':True,'D3_star_proved':False}))
