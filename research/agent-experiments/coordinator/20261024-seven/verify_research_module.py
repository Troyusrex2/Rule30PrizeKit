"""Generic guarded replay of a named owned research source, at the exact pin."""
import argparse,hashlib,importlib.util,json,shutil
from pathlib import Path
from core import HERE,REPO
from verification_context import add_reference_options,reference,unchanged,identity

def main():
    parser=argparse.ArgumentParser(description=__doc__);add_reference_options(parser)
    parser.add_argument('--module',required=True);parser.add_argument('--headlines',nargs='+',required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();project,lake,checker=reference(args)
    assert args.module.isidentifier()
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    source=HERE/(args.module+'.lean');raw=source.read_bytes();target=project/source.name
    if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different owned module exists')
    shutil.copyfile(source,target);obj=project/'.lake/build/lib/lean'/(args.module+'.olean')
    build=guard.guarded([str(lake),'env','lean','-o',str(obj),str(target)],project,out/'build.log')
    argv=[str(lake),'env','lean','--run','Check.lean',args.module,'--claim','partial']
    for h in args.headlines:argv+=['--headline',h if '.' in h else args.module+'.'+h]
    replay=guard.guarded(argv,project,out/'check.log')
    checked=json.loads([s for s in (out/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
    assert all(h['ok'] for h in checked['headlines']) and target.read_bytes()==raw
    unchanged(project,checker)
    result={**identity(checker),'source_sha256':hashlib.sha256(raw).hexdigest(),
            'build_seconds':build,'replay_seconds':replay,'check':checked,'full_problem_solved':False}
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'verdict':'pass','constants':checked['replay']['constants'],'headlines':len(args.headlines)},flush=True)

if __name__=='__main__':main()
