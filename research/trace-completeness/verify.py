"""Fully replay the trace laws, obstructions, inverse code, and seed reduction."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('stripe_replay',HERE.parent/'normalization-first-meeting/replay.py')
replay=importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)
NS='Rule30NormalizationMachineResearch.'
ITEMS=[('Rule30PairedForcingResearch',['local_polarization','paired_difference_step',
                                     'local_center_gate','same_center_gate']),
       ('Rule30TraceHorizonCounterexampleResearch',['pair58_prefix','pair58_difference',
           'pair58_no_early_stripe','linear_full_recovery_counterexample']),
       ('Rule30InverseTraceResearch',['InverseTrace.inversePrefix_lt','InverseTrace.inversePrefix_right',
          'InverseTrace.inversePrefix_realizes','InverseTrace.finite_trace_code_injective',
          'InverseTrace.inversePrefix_unique']),
       ('Rule30EdgeHorizonObstructionResearch',['pair13_prefix','pair13_difference',
          'pair13_distinct_edges','edge_horizon_2n_minus_c_counterexample',
          'edge_horizon_2n_minus_one_counterexample']),
       ('Rule30SeedBoundaryResearch',['SeedBoundary.seedLow_phiRows',
          'SeedBoundary.seedLow_stripe_trivial','SeedBoundary.seedLow_even_never_stripe',
          'SeedBoundary.period_pair_never_stripe','SeedBoundary.seedRows_sound',
          'SeedBoundary.aligned_seed_read','SeedBoundary.period_pair_left_outside',
          'SeedBoundary.periodic_center_forces_seed_even_collision',
          'SeedBoundary.problem1_of_seedLow_even_left_separation'])]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,required=True)
    parser.add_argument('--lake',required=True)
    args=parser.parse_args()
    project=args.project.resolve()
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==replay.KIT
    checker=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    manifest=json.loads((HERE.parent/'normalization-first-meeting/evidence/manifest.json').read_text())
    for module in manifest['modules']:
        assert hashlib.sha256((project/(module['module']+'.lean')).read_bytes()).hexdigest()==module['source_sha256']
    evidence=HERE/'evidence'
    logs=evidence/'logs'
    logs.mkdir(parents=True,exist_ok=True)
    records=[]
    for module,heads in ITEMS:
        source=HERE/(module+'.lean')
        target=project/source.name
        if target.exists() and target.read_bytes()!=source.read_bytes():
            raise RuntimeError('Different research source exists: '+str(target))
        target.write_bytes(source.read_bytes())
        seconds=replay.guarded([args.lake,'env','lean','-o',
            str(project/'.lake/build/lib/lean'/(module+'.olean')),str(target)],project,logs/(module+'.build.log'))
        argv=[args.lake,'env','lean','--run','Check.lean',module,'--claim','partial']
        for head in heads:argv+=['--headline',NS+head]
        log=logs/(module+'.check.log')
        elapsed=replay.guarded(argv,project,log)
        check=json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
        assert check['verdict']=='pass' and check['replay']['ok'] and not check['newAxioms']
        assert all(h['ok'] for h in check['headlines'])
        records.append({'module':module,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                        'compile_seconds':seconds,'replay_seconds':elapsed,'check':check})
        print(json.dumps({'module':module,'verdict':'pass','constants':check['replay']['constants']}),flush=True)
    (evidence/'report.json').write_text(json.dumps({'verdict':'pass','kit_commit':replay.KIT,
        'checker_unchanged':True,'modules':records,'edge_observability_proved':False,
        'trace_completeness_proved':False,'full_problem_solved':False},indent=2)+'\n',encoding='utf-8',newline='\n')

if __name__=='__main__':main()
