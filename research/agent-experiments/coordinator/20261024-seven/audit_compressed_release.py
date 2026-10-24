"""Check published and staged bytes against the release and replay records."""
import hashlib,json,subprocess
from core import REPO

def main():
    rel='research/agent-experiments/coordinator/20261024-seven';dest=REPO/rel
    manifest=json.loads((dest/'compressed-artifacts.json').read_text(encoding='utf-8'))
    for name,sha in manifest['files'].items():
        raw=(dest/name).read_bytes();assert hashlib.sha256(raw).hexdigest()==sha,name
        staged=subprocess.check_output(['git','show',':'+rel+'/'+name],cwd=REPO)
        assert staged==raw,('staged bytes differ',name)
    old=json.loads((dest/'catalog-artifacts.json').read_text(encoding='utf-8'))
    for name,sha in old['files'].items():
        assert hashlib.sha256((dest/name).read_bytes()).hexdigest()==sha,('earlier manifest',name)
    pairs=[('Rule30FrontLanesResearch.lean','front-lanes-evidence/report.json'),
           ('Rule30FrontReturnMapResearch.lean','front-return-map-evidence/report.json'),
           ('front-jump/Rule30FrontJumpMapResearch.lean','front-jump/map-evidence/report.json'),
           ('front-jump/Rule30FrontJumpCycleResearch.lean','front-jump/cycle-evidence/report.json')]
    generation=json.loads((dest/'front-jump/generation.json').read_text(encoding='utf-8'))
    pairs += [('front-jump/'+e['module']+'.lean','front-jump/evidence/'+e['module']+'.json')
              for e in generation['entries']]
    counts=0
    for source,report in pairs:
        result=json.loads((dest/report).read_text(encoding='utf-8'))
        assert result['source_sha256']==hashlib.sha256((dest/source).read_bytes()).hexdigest()
        check=result['check'];assert check['verdict']=='pass' and check['replay']['ok'] and not check['newAxioms']
        assert all(h['ok'] for h in check['headlines']);counts+=check['replay']['constants']
    print({'release_files':len(manifest['files']),'checked_sources':len(pairs),
           'replayed_declarations':counts,'staged_bytes_match':True},flush=True)

if __name__=='__main__':main()
