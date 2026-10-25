"""Independent full replay of the exact public 8d7751 contribution."""
import argparse,hashlib,importlib.util,json,shutil,urllib.request
from core import HERE,REPO
from verification_context import add_reference_options,reference,unchanged,identity

def main():
    parser=argparse.ArgumentParser(description=__doc__);add_reference_options(parser)
    project,lake,checker=reference(parser.parse_args())
    source=HERE/'external/HerbertAbsorbedPrefixes-8d7751.lean'
    if not source.exists():
        source.parent.mkdir(exist_ok=True)
        source.write_bytes(urllib.request.urlopen('https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/file?id=R30-20261024-8d7751&kind=lean',timeout=45).read())
    raw=source.read_bytes()
    sha='b0113490bddc1abcc9c9d30b5f6a250108120ddd87de65bd7654d0d42fd89ff5'
    assert hashlib.sha256(raw).hexdigest()==sha
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=HERE/'external/8d7751-evidence';out.mkdir(exist_ok=True)
    mod='Rule30ExternalAbsorbedPrefixesAudit';target=project/(mod+'.lean')
    if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different external source exists')
    shutil.copyfile(source,target);obj=project/'.lake/build/lib/lean'/(mod+'.olean')
    build=guard.guarded([str(lake),'env','lean','-o',str(obj),str(target)],project,out/'build.log')
    heads=['CQ01_prefix31','CQ01_prefix495','Psi_prefix31','Psi_prefix495','Psi_eq',
           'CQ01_fam','fam_injective','not_move_equivalent','drv_prefix_agree','u_prefix31','u_prefix495']
    argv=[str(lake),'env','lean','--run','Check.lean',mod,'--claim','partial']
    for h in heads:argv+=['--headline','Rule30Submission.'+h]
    replay=guard.guarded(argv,project,out/'check.log')
    checked=json.loads([s for s in (out/'check.log').read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
    assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
    assert all(h['ok'] for h in checked['headlines']) and target.read_bytes()==raw
    unchanged(project,checker)
    result={**identity(checker),'source_sha256':sha,'source_id':'R30-20261024-8d7751',
            'authors':'Gareth Herbert; Claude (Anthropic); GPT (OpenAI)',
            'build_seconds':build,'replay_seconds':replay,'check':checked,'full_problem_solved':False}
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'verdict':'pass','constants':checked['replay']['constants'],'headlines':len(heads)},flush=True)

if __name__=='__main__':main()
