"""Replay the constructive even-depth decoder and its exact external dependency.

No period exclusion, Q01 proof or full prize solution is asserted.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
KIT = '3eca23c0a9fa6b153313655e6d51835406c2d06e'
EXTERNAL_SHA = '153226d13365d8b01d4e85a4ecac57b0556e59c98cdbff1d8dc74f6e39c6daa0'
MODULE = 'Rule30EvenDecodeResearch'
HEADS = ['evenCode_decode', 'evenCode_injective', 'decode_evenCode',
         'evenCode_bijective', 'decode_locality', 'oddCode_locality',
         'finite_even_odd_iff', 'Q01_iff_finite_even_infinite_odd']
SENSITIVITY = 'Rule30OddSensitivityResearch'
SENSITIVITY_HEADS = ['recon_shoulder_difference', 'shoulder_parity',
                     'recon_flipAt', 'alt_flipAt', 'odd_free_flip']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--lake', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    project = args.project.resolve()
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==KIT
    checker = subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    spec = importlib.util.spec_from_file_location('guard',
        HERE.parent/'normalization-first-meeting/replay.py')
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    out = args.output.resolve()
    out.mkdir(parents=True,exist_ok=True)
    guard.guarded([sys.executable,str(HERE.parent/'catalog-review/audit_skelpair_submission.py'),
                   '--project',str(project),'--lake',args.lake,'--output',str(out/'parent')],
                  project,out/'parent-audit.log')
    parent = json.loads((out/'parent/skelpair-report.json').read_text(encoding='utf-8'))
    assert parent['verdict']=='pass' and parent['source_sha256']==EXTERNAL_SHA
    assert parent['check']['replay']=={'constants':139,'ok':True}
    source = HERE/(MODULE+'.lean')
    raw = source.read_bytes()
    target = project/source.name
    if target.exists() and target.read_bytes()!=raw:
        raise RuntimeError('Different research source exists: '+str(target))
    shutil.copyfile(source,target)
    obj = project/'.lake/build/lib/lean'/(MODULE+'.olean')
    build = guard.guarded([args.lake,'env','lean','-o',str(obj),str(target)],project,out/'build.log')
    print(json.dumps({'stage':'compiled','seconds':build}),flush=True)
    argv = [args.lake,'env','lean','--run','Check.lean',MODULE,'--claim','partial']
    for h in HEADS: argv += ['--headline',MODULE+'.'+h]
    log = out/'check.log'
    replay = guard.guarded(argv,project,log)
    check = json.loads([s for s in log.read_text(encoding='utf-8').splitlines()
                        if s.startswith('{')][-1])
    assert check['verdict']=='pass' and check['replay']=={'constants':31,'ok':True}
    assert not check['newAxioms'] and len(check['headlines'])==len(HEADS)
    assert all(h['ok'] for h in check['headlines'])
    assert source.read_bytes()==raw==target.read_bytes()
    # The sensitivity theorem uses only the official kit, not the external
    # reconstruction. Build and replay it separately with the same checker.
    extra_source = HERE/(SENSITIVITY+'.lean')
    extra_raw = extra_source.read_bytes()
    extra_target = project/extra_source.name
    if extra_target.exists() and extra_target.read_bytes()!=extra_raw:
        raise RuntimeError('Different research source exists: '+str(extra_target))
    shutil.copyfile(extra_source,extra_target)
    extra_deps = guard.guarded([args.lake,'build',
        'Ruliology.CellularAutomata.Rule30ZeroBoundary'],project,out/'sensitivity-dependencies.log')
    extra_obj = project/'.lake/build/lib/lean'/(SENSITIVITY+'.olean')
    extra_build = guard.guarded([args.lake,'env','lean','-o',str(extra_obj),str(extra_target)],
                               project,out/'sensitivity-build.log')
    print(json.dumps({'stage':'sensitivity_compiled','seconds':extra_build}),flush=True)
    extra_argv = [args.lake,'env','lean','--run','Check.lean',SENSITIVITY,'--claim','partial']
    for h in SENSITIVITY_HEADS: extra_argv += ['--headline',SENSITIVITY+'.'+h]
    extra_log = out/'sensitivity-check.log'
    extra_replay = guard.guarded(extra_argv,project,extra_log)
    extra_check = json.loads([s for s in extra_log.read_text(encoding='utf-8').splitlines()
                             if s.startswith('{')][-1])
    assert extra_check['verdict']=='pass' and extra_check['replay']=={'constants':41,'ok':True}
    assert not extra_check['newAxioms'] and len(extra_check['headlines'])==len(SENSITIVITY_HEADS)
    assert all(h['ok'] for h in extra_check['headlines'])
    assert extra_source.read_bytes()==extra_raw==extra_target.read_bytes()
    assert hashlib.sha256((project/'Rule30ExternalSkelPairAudit.lean').read_bytes()).hexdigest()==EXTERNAL_SHA
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    report = {'verdict':'pass','kit_commit':KIT,'source_sha256':hashlib.sha256(raw).hexdigest(),
              'checker_sha256':hashlib.sha256(checker).hexdigest(),'checker_unchanged':True,
              'external_reconstruction_audit':parent,'build_seconds':build,
              'replay_seconds':replay,'check':check,
              'odd_sensitivity':{'module':SENSITIVITY,
                'source_sha256':hashlib.sha256(extra_raw).hexdigest(),
                'dependency_build_seconds':extra_deps,'build_seconds':extra_build,
                'replay_seconds':extra_replay,'check':extra_check},
              'Q01_proved':False,
              'full_problem_solved':False}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'verdict':'pass','own_declarations':72,'own_headlines':13,
                      'external_declarations':139}),flush=True)


if __name__=='__main__': main()
