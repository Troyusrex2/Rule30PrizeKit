"""Extract the owned, hashed payload and create an isolated pinned checkout."""
import argparse,hashlib,json,subprocess,sys,zipfile
from pathlib import Path,PurePosixPath

def digest(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

def main():
    p=argparse.ArgumentParser();p.add_argument('--archive-sha',required=True);a=p.parse_args()
    root=Path.home()/'Rule30-offload'
    assert (root/'OWNER.txt').read_text().strip()=='Rule30 research worker; created 2026-10-25'
    archive=root/'_cache/g913-lean-payload.zip';transfer=json.loads((root/'_cache/transfer-manifest.json').read_text())
    assert digest(archive)==a.archive_sha==transfer['archive_sha256']
    payload=root/'_cache/payload';payload.mkdir(exist_ok=True)
    with zipfile.ZipFile(archive) as z:
        for entry in z.infolist():
            pp=PurePosixPath(entry.filename)
            assert not pp.is_absolute() and '..' not in pp.parts and ':' not in entry.filename
        z.extractall(payload)
    manifest=json.loads((payload/'payload-manifest.json').read_text())
    ref=root/'reference'
    if not ref.exists():
        subprocess.run(['git','-c','core.autocrlf=false','clone','--no-checkout',str(payload/'kit.bundle'),str(ref)],check=True)
        subprocess.run(['git','-c','core.autocrlf=false','-C',str(ref),'checkout','--detach',manifest['kit_commit']],check=True)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ref,text=True).strip()==manifest['kit_commit']
    assert digest(ref/'Check.lean')==manifest['checker_sha256']
    notes=root/'NOTES.md'
    if not notes.exists():notes.write_text('# Rule 30 worker notes\n\nPinned kit '+manifest['kit_commit']+
        '. The official checker is unchanged. The initial job rebuilds nine dependencies and retries one formerly memory-limited leaf.\n'+
        'Results live under results/. Cache/toolchain/bundle are reproducible under _cache/.\n'+
        'Initial compute guard: 300 seconds, 16 GiB per process tree, at least 16 GiB system RAM free.\n',encoding='utf-8')
    print({'bootstrap':'verified','files':len(manifest['files']),'kit_commit':manifest['kit_commit']},flush=True)
    sys.exit(subprocess.call([sys.executable,str(payload/'worker.py'),'--root',str(root),'--probe']))

if __name__=='__main__':main()
