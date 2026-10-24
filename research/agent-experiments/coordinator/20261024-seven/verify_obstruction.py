"""Pinned compile and full unchanged official checker replay."""
import argparse,hashlib,json,shutil,subprocess
from pathlib import Path
from core import BASE,HERE,REPO
import importlib.util

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,default=BASE/'current-reference-3eca-20261024')
    parser.add_argument('--lake',type=Path,default=BASE/'toolchain/lean-4.35.0-windows/bin/lake.exe')
    args=parser.parse_args();project=args.project.resolve()
    pin='3eca23c0a9fa6b153313655e6d51835406c2d06e'
    lake=args.lake.resolve()
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==pin
    checker=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=HERE/'lean-evidence';out.mkdir(exist_ok=True)
    dep=guard.guarded([str(lake),'build','Ruliology.CellularAutomata.Rule30StripeMeeting'],project,out/'dependencies.log')
    mod='Rule30ReaderObstructionResearch';source=HERE/(mod+'.lean');target=project/source.name
    raw=source.read_bytes()
    if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different source exists; review before replacing')
    shutil.copyfile(source,target)
    obj=project/'.lake/build/lib/lean'/(mod+'.olean')
    build=guard.guarded([str(lake),'env','lean','-o',str(obj),str(target)],project,out/'build.log')
    heads=['pair48_49_classes','pair48_49_equal27','pair48_49_equal25','pair48_49_first_difference',
           'no_four_width_generic_reader','coupled_difference','center_successor_does_not_determine_right']
    argv=[str(lake),'env','lean','--run','Check.lean',mod,'--claim','partial']
    for h in heads:argv+=['--headline',mod+'.'+h]
    replay=guard.guarded(argv,project,out/'check.log')
    checked=json.loads([s for s in (out/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
    assert all(h['ok'] for h in checked['headlines']) and len(checked['headlines'])==len(heads)
    assert target.read_bytes()==raw and (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    result={'kit_commit':pin,'source_sha256':hashlib.sha256(raw).hexdigest(),
            'checker_sha256':hashlib.sha256(checker).hexdigest(),'checker_unchanged':True,
            'dependency_seconds':dep,'build_seconds':build,'replay_seconds':replay,
            'check':checked,'full_problem_solved':False,'edge_separation_refuted':False}
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print({'status':'pass','declarations':checked['replay']['constants'],'headlines':len(heads)},flush=True)

if __name__=='__main__':main()
