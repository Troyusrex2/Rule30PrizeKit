from pathlib import Path
import hashlib, json, re

root = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
files = json.loads((root/'artifacts.json').read_bytes())['files']
for name,digest in files.items():
    path = (root/name).resolve()
    assert path.is_relative_to(root) and sha(path) == digest, name
summary = json.loads((root/'summary.json').read_bytes())
seen = set()
for item in summary['root_fresh_replays']:
    name = item['module']
    report = json.loads((root/'formal'/name/'report.json').read_bytes())
    check = report['checker']
    guard = json.loads((root/'evidence'/('replay-'+name+'.guard.json')).read_bytes())
    source = root/'sources'/(name+'.lean')
    assert sha(source) == report['source_sha256'] == item['source_sha256']
    assert report['pin'] == summary['pin'] and report['checker_sha256'] == summary['checker_sha256']
    assert report['passed'] and check['verdict'] == 'pass'
    assert check['replay'] == {'ok':True,'constants':item['module_constants_including_internal']}
    assert not check['newAxioms'] and not check['verifiedTargets']
    assert all(h['ok'] and h['typeMatches'] for h in check['headlines'])
    assert guard['exit_code'] == 0 and guard['guard_stop'] is None
    assert guard['elapsed_seconds'] < 300 and guard['peak_owned_rss_bytes'] < 8*1024**3
    assert guard['minimum_system_available_bytes'] >= 2*1024**3
    for imported in re.findall(rb'^import\s+(\S+)', source.read_bytes(), re.M):
        imported = imported.decode()
        assert imported.startswith('Ruliology.') or imported in seen
    seen.add(name)
assert set(summary['build_order']) == seen == {p.stem for p in (root/'sources').glob('*.lean')}
assert sum(x['module_constants_including_internal'] for x in summary['root_fresh_replays']) == 372
assert not summary['P1_proved'] and not summary['automatic_linear_padding_entry_proved']
print(json.dumps({'passed':True,'artifact_hashes':len(files),'modules':len(seen),'module_constants_including_internal':372,'prize_solved':False}))
