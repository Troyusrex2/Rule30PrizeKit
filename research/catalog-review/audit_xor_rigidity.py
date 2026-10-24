"""Independently replay PR 12's exact proof with module wrappers removed."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'overnight'))
from audit_contributions import run

COMMIT = 'e7d1e3a03dff9c57a0c78e94b7bf9e4df1c0bd36'
RELATIVE = 'lean/Ruliology/CellularAutomata/Rule30XorRigidity.lean'
MODULE = 'Rule30ExternalXorRigidityE7DReview'
NS = 'Ruliology.CellularAutomata.Rule30XorRigidity.'
HEADS = ['HalfLine.local_cross','HalfLine.distant_good','HalfLine.all_good',
         'all_good','actual_add_classification','shear_actual_iff',
         'standard_add_classification','standard_full_classification',
         'standard_two_partners','xor_history_iff']

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,required=True)
    parser.add_argument('--source-repository',type=Path,required=True)
    parser.add_argument('--lake',required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--trace-barrier',action='store_true',
                        help='Also replay the finite-row equal-trace/XOR counterexample; first run normalization-first-meeting/replay.py')
    args = parser.parse_args()
    root = args.project.resolve()
    args.output.mkdir(parents=True,exist_ok=True)
    kit = subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
    assert kit=='2f63afda261888e04ec57237290e723190914a1d'
    checker = subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=root)
    assert (root/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    raw = subprocess.check_output(['git','show',COMMIT+':'+RELATIVE],cwd=args.source_repository)
    source = raw.decode('utf-8').removeprefix('module\n\n')
    source = source.replace('public import ','import ').replace('@[expose] public section\n\n','')
    target = root/(MODULE+'.lean')
    if target.exists() and target.read_text(encoding='utf-8')!=source:
        raise RuntimeError('Different review source already exists: '+str(target))
    target.write_text(source,encoding='utf-8',newline='\n')
    artifact = root/'.lake/build/lib/lean'/(MODULE+'.olean')
    seconds = run([args.lake,'env','lean','-o',str(artifact),str(target)],root,
                  args.output/'compile.log',timeout=300)
    print(json.dumps({'module':MODULE,'stage':'compiled','seconds':round(seconds,3)}),flush=True)
    argv = [args.lake,'env','lean','--run','Check.lean',MODULE,'--claim','partial']
    for head in HEADS:
        argv += ['--headline',NS+head]
    log = args.output/'check.log'
    check_seconds = run(argv,root,log,timeout=300)
    checked = json.loads([s for s in log.read_text(encoding='utf-8').splitlines()
                          if s.startswith('{')][-1])
    assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
    assert all(h['ok'] for h in checked['headlines'])
    report = {'verdict':'pass','source_commit':COMMIT,'source_path':RELATIVE,
              'source_sha256':hashlib.sha256(raw).hexdigest(),
              'adapted_source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
              'adaptations':'module/public import/export wrappers only; namespace and proof bodies unchanged',
              'kit_commit':kit,'checker_unchanged':True,
              'checker_sha256':hashlib.sha256(checker).hexdigest(),
              'build_seconds':round(seconds,3),'replay_seconds':round(check_seconds,3),
              'authors':'OpenAI Codex for @AIOvernight; pull request assembled with Claude Code',
              'check':checked,'problem1_proved':False,
              'scope':'XOR of two ordinary whole-line Rule 30 histories is a history iff one is zero or they are identical; equal center traces alone do not imply that premise'}
    if args.trace_barrier:
        research = Path(__file__).resolve().parents[1]/'normalization-first-meeting'
        manifest = json.loads((research/'evidence/manifest.json').read_text(encoding='utf-8'))
        for item in manifest['modules']:
            dependency = root/(item['module']+'.lean')
            assert hashlib.sha256(dependency.read_bytes()).hexdigest()==item['source_sha256']
        name = 'Rule30XorTraceBarrierResearch'
        own_source = Path(__file__).resolve().parent/(name+'.lean')
        own_target = root/own_source.name
        if own_target.exists() and own_target.read_bytes()!=own_source.read_bytes():
            raise RuntimeError('Different trace-barrier source exists: '+str(own_target))
        own_target.write_bytes(own_source.read_bytes())
        elapsed = run([args.lake,'env','lean','-o',str(root/'.lake/build/lib/lean'/(name+'.olean')),
                       str(own_target)],root,args.output/'trace-barrier.compile.log',timeout=300)
        own_heads = ['two_three_stripe_related','two_three_entire_trace','same_trace_does_not_imply_xor_step']
        command = [args.lake,'env','lean','--run','Check.lean',name,'--claim','partial']
        for head in own_heads:
            command += ['--headline','Rule30NormalizationMachineResearch.'+head]
        own_log = args.output/'trace-barrier.check.log'
        replay_seconds = run(command,root,own_log,timeout=300)
        own_check = json.loads([s for s in own_log.read_text(encoding='utf-8').splitlines()
                                if s.startswith('{')][-1])
        assert own_check['verdict']=='pass' and own_check['replay']['ok'] and not own_check['newAxioms']
        assert all(h['ok'] for h in own_check['headlines'])
        report['trace_barrier'] = {'module':name,'source_sha256':hashlib.sha256(own_source.read_bytes()).hexdigest(),
                                  'build_seconds':round(elapsed,3),'replay_seconds':round(replay_seconds,3),
                                  'check':own_check,'authors':'Troy Lowry; OpenAI Codex',
                                  'scope':'Rows 2 and 3 at center 1 have equal entire traces but their XOR difference fails the Rule 30 update on the first step'}
    (args.output/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'verdict':'pass','constants':checked['replay']['constants'],
                      'headlines':len(checked['headlines'])}),flush=True)

if __name__=='__main__':
    main()
