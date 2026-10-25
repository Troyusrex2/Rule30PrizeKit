"""Audit release hashes, then replay every declaration with the official checker."""
import argparse,hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
from core import HERE,REPO
from verification_context import add_reference_options,reference

def main():
    p=argparse.ArgumentParser();add_reference_options(p);p.add_argument('--audit-only',action='store_true')
    p.add_argument('--output',type=Path,default=HERE/'language-budget-replay');a=p.parse_args()
    manifest=json.loads((HERE/'language-budget-artifacts.json').read_text(encoding='utf-8'))
    for name,sha in manifest['files'].items():assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==sha,name
    for m in manifest['modules']:
        assert hashlib.sha256((HERE/(m['module']+'.lean')).read_bytes()).hexdigest()==m['source_sha256']
        r=json.loads((HERE/m['report']).read_text(encoding='utf-8'));ck=r['check']
        assert r['source_sha256']==m['source_sha256'] and r['kit_commit']==manifest['kit_commit'] and r['checker_unchanged']
        assert r['checker_sha256']==manifest['checker_sha256'] and ck['verdict']=='pass' and ck['replay']['ok']
        assert not ck['newAxioms'] and all(h['ok'] for h in ck['headlines'])
    print({'artifact_hash_audit':'pass','modules':len(manifest['modules'])},flush=True)
    if a.audit_only:return
    project,lake,_=reference(a);a.output.mkdir(parents=True,exist_ok=True)
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    guard.guarded([str(lake),'build','Ruliology.CellularAutomata.Rule30CenterRuns'],project,a.output/'imports-build.log')
    for m in manifest['modules']:
        subprocess.run([sys.executable,str(HERE/'verify_research_module.py'),'--module',m['module'],
            '--headlines',*m['headlines'],'--project',str(project),'--lake',str(lake),
            '--output',str(a.output/m['module'])],cwd=HERE,check=True)

if __name__=='__main__':main()
