"""Fresh guarded replay of every published even-support component in order."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
from core import HERE
from verification_context import add_reference_options,reference,unchanged

def main():
    parser=argparse.ArgumentParser(description=__doc__);add_reference_options(parser)
    parser.add_argument('--output',type=Path,default=HERE/'fresh-even-support-replay')
    parser.add_argument('--resume',action='store_true');args=parser.parse_args()
    project,lake,checker=reference(args)
    manifest=json.loads((HERE/'even-support-artifacts.json').read_text(encoding='utf-8'))
    for item in manifest['modules']:
        module=item['module'];source=HERE/(module+'.lean');raw=source.read_bytes()
        assert hashlib.sha256(raw).hexdigest()==item['source_sha256']
        out=args.output.resolve()/module;report=out/'report.json'
        target=project/source.name
        if args.resume and report.exists() and (project/'.lake/build/lib/lean'/(module+'.olean')).exists():
            r=json.loads(report.read_text(encoding='utf-8'))
            assert r['source_sha256']==item['source_sha256'] and target.read_bytes()==raw
            assert r['kit_commit']==manifest['kit_commit'] and r['checker_sha256']==manifest['checker_sha256']
            assert r['check']['verdict']=='pass' and r['check']['replay']['ok'] and not r['check']['newAxioms']
            assert all(h['ok'] for h in r['check']['headlines'])
            print({'module':module,'stage':'retained_exact_source_pass'},flush=True);continue
        print({'module':module,'stage':'fresh_build_and_replay'},flush=True)
        subprocess.run([sys.executable,str(HERE/'verify_research_module.py'),
            '--module',module,'--headlines',*item['headlines'],'--project',str(project),
            '--lake',str(lake),'--output',str(out)],cwd=HERE,check=True)
        unchanged(project,checker)
    print({'all_modules_passed':True,'full_problem_solved':False},flush=True)

if __name__=='__main__':main()
