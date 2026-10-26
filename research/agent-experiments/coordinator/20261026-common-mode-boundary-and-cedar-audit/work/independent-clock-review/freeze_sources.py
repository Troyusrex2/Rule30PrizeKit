"""Freeze the requested published package, without executing its programs."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parent
REPO=Path('D:/MWB/Rule30/overnight-20261024')
COMMIT='64197054b1e4f5b768a624c16bd3c1db0555f3cb'
PREFIX='research/agent-experiments/coordinator/20261026-periodic-or-clock-transfer/'
out=ROOT/'published';out.mkdir(exist_ok=False)
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',COMMIT,'--',PREFIX],cwd=REPO).decode().splitlines()
assert paths
files={}
for name in paths:
    assert name.startswith(PREFIX)
    relative=name[len(PREFIX):];target=out/relative
    assert target.resolve().is_relative_to(out.resolve())
    data=subprocess.check_output(['git','show',COMMIT+':'+name],cwd=REPO)
    target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    files[relative]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),published_path=name)
manifest=dict(commit=COMMIT,repository=str(REPO),package_prefix=PREFIX,files=files,
    status='Frozen exact published bytes; no producer code executed')
(ROOT/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(commit=COMMIT,files=len(files),bytes=sum(x['bytes'] for x in files.values())),indent=2))
