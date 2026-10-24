"""Fresh replay of the exact public Lean-verified f177ae source."""
import argparse,hashlib,importlib.util,json,shutil,subprocess,urllib.request
from pathlib import Path
from core import HERE,REPO,BASE

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,default=BASE/'current-reference-3eca-20261024')
    parser.add_argument('--lake',type=Path,default=BASE/'toolchain/lean-4.35.0-windows/bin/lake.exe')
    args=parser.parse_args()
    src=HERE/'external/QuintGeminiFiveTail-f177ae.lean'
    if not src.exists():
        src.parent.mkdir(exist_ok=True)
        src.write_bytes(urllib.request.urlopen('https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/file?id=R30-20261024-f177ae&kind=lean',timeout=45).read())
    raw=src.read_bytes()
    sha='b84849e8f368b030550f586f1c2808e3da74e28e9d93b6b99d808de4f9942689'
    assert hashlib.sha256(raw).hexdigest()==sha
    pin='3eca23c0a9fa6b153313655e6d51835406c2d06e'
    project=args.project.resolve()
    lake=args.lake.resolve()
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==pin
    checker=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=HERE/'external/f177ae-evidence';out.mkdir(exist_ok=True)
    deps=guard.guarded([str(lake),'build','Rule30PrizeKit','Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFour'],project,out/'dependencies.log')
    mod='Rule30ExternalFiveTailAudit';target=project/(mod+'.lean')
    if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different external source exists')
    shutil.copyfile(src,target);obj=project/'.lake/build/lib/lean'/(mod+'.olean')
    print({'stage':'compile'},flush=True)
    build=guard.guarded([str(lake),'env','lean','-o',str(obj),str(target)],project,out/'build.log')
    heads=['stripe_five_tail','family5_of_odd_defect','family5_of_class','front_sound_13',
           'stripe_four_tail_13_mod65536','stripe_five_tail_27_mod65536','control_13_61005_false',
           *['cyc5_'+str(i) for i in range(17,32,2)],'cyc13_period','cyc13_sig']
    argv=[str(lake),'env','lean','--run','Check.lean',mod,'--claim','partial']
    for h in heads:argv+=['--headline','Rule30Submission.'+h]
    print({'stage':'full_kernel_replay','build_seconds':build},flush=True)
    replay=guard.guarded(argv,project,out/'check.log')
    checked=json.loads([s for s in (out/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
    assert all(h['ok'] for h in checked['headlines'])
    assert target.read_bytes()==raw and (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    report={'source_id':'R30-20261024-f177ae','authors':'G.P.J.W. Quint; Gemini (Google)',
            'source_sha256':sha,'kit_commit':pin,'checker_unchanged':True,
            'checker_sha256':hashlib.sha256(checker).hexdigest(),'dependency_seconds':deps,
            'build_seconds':build,'replay_seconds':replay,'check':checked,'full_problem_solved':False}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print({'status':'pass','declarations':checked['replay']['constants'],'headlines':len(heads)},flush=True)

if __name__=='__main__':main()
