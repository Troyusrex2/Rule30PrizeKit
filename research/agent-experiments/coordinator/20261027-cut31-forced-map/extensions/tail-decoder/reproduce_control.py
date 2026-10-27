"""Optional exact two-history control; write only a new runs directory, never retained evidence."""
from pathlib import Path
import argparse,datetime,hashlib,json,re,shutil,subprocess,sys
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--run-name')
args=parser.parse_args()
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for item in json.loads((root/'MANIFEST.json').read_text())['files']:
    assert sha(root/item['path'])==item['sha256']
name=args.run_name or datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
assert re.fullmatch(r'[A-Za-z0-9_-]+',name)
run=root/'runs'/('control-'+name);run.mkdir(parents=True,exist_ok=False)
for name in ['probe.py','PROTOCOL.md']:shutil.copyfile(root/'factor-control'/name,run/name)
subprocess.run([sys.executable,'-B',str(run/'probe.py')],cwd=run,check=True)
expected=json.loads((root/'factor-control/RESULT.json').read_text())
actual=json.loads((run/'RESULT.json').read_text())
assert actual['script_sha256']==sha(run/'probe.py')
assert actual['protocol_sha256']==sha(run/'PROTOCOL.md')
for obj in [expected,actual]:
    obj.pop('elapsed_seconds');obj.pop('protocol_sha256')
assert actual==expected
assert json.loads((run/'CONES.json').read_text(encoding='utf-8'))==json.loads((root/'factor-control/CONES.json').read_text(encoding='utf-8'))
print(json.dumps({'passed':True,'scope':'Exactly the two retained fixed histories and stencil window; no extra search.'}))
