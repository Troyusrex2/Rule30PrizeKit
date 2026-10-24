"""Rebuild all proof layers and replay the unchanged official Lean checker.

Requires Python 3 and psutil. Every owned compiler/replay process is guarded.
No assertion about prize status or infinite-trace completeness is made.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time
import psutil

HERE = Path(__file__).resolve().parent
KIT = '2f63afda261888e04ec57237290e723190914a1d'
NS = 'Rule30NormalizationMachineResearch.'
LAYERS = [
    ('Machine', ['checked']),
    ('MachineSoundness', ['initial_member','step_member','run_member','all_input_lengths_safe']),
    ('Window', ['Phi_testBit','first_exact','second_exact','history_succ']),
    ('Packing', ['View.decode_encode','symbol_lt','symbol_bits','relStep_lt']),
    ('Stream', ['View.encode_advance','View.advance_valid','View.run_encode','safe_after_input']),
    ('ActualInput', ['centerCode_succ','actualView_advance','actualInput_run','actual_input_safe']),
    ('Relation', ['relationRun_code','identAt_iff','validAt_iff','relationRun_accept_iff']),
    ('CommonCut', ['flush_actual','View.accept_encode','relationRun_full_iff','two_step_common_cut']),
    ('TailLanguage', ['tailFold_accept_iff','tailRun_accept_iff',
                      'rowRelated_iff_stripeRelated','two_step_stripe_related']),
    ('FirstMeeting', ['stripe_meeting_is_early','no_delayed_stripe_meeting']),
    ('Rule30StripePreservationResearch', ['preservesTwo_pool','StripeRelated.center_pair',
                                        'preservesTwo_after_actual','stripe_related_preserves_two']),
    ('Rule30StripeTraceResearch', ['phiRows_add','stripe_related_same_trace',
                                 'stripe_related_same_prefix','eventually_stripe_iff_early']),
]

def sha(data):
    return hashlib.sha256(data).hexdigest()

def guarded(argv, cwd, log):
    started = time.monotonic()
    with log.open('w',encoding='utf-8',newline='\n') as stream:
        process = subprocess.Popen(argv,cwd=cwd,stdout=stream,stderr=subprocess.STDOUT)
        owner = psutil.Process(process.pid)
        try:
            while process.poll() is None:
                time.sleep(.5)
                try:
                    children = [owner] + owner.children(recursive=True)
                except psutil.NoSuchProcess:
                    children = []
                rss = 0
                for child in children:
                    try:
                        rss += child.memory_info().rss
                    except psutil.NoSuchProcess:
                        pass
                if (rss > 8*1024**3 or psutil.virtual_memory().available < 2*1024**3
                        or time.monotonic()-started > 300):
                    raise RuntimeError('Owned job exceeded resource guard; no pass claimed')
            if process.returncode:
                raise RuntimeError(log.read_text(encoding='utf-8')[-3000:])
        finally:
            if process.poll() is None:
                try:
                    children = owner.children(recursive=True) + [owner]
                except psutil.NoSuchProcess:
                    children = []
                for child in reversed(children):
                    try:
                        child.kill()
                    except psutil.NoSuchProcess:
                        pass
                process.wait()
    return round(time.monotonic()-started,3)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,required=True)
    parser.add_argument('--lake',required=True)
    parser.add_argument('--output',type=Path,default=HERE/'evidence')
    parser.add_argument('--replace-research-sources',action='store_true',
                        help='Allow replacement of these named research modules only')
    parser.add_argument('--resume',action='store_true',
                        help='Retain exact-source passing reports from this output directory')
    args = parser.parse_args()
    project = args.project.resolve()
    actual = subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()
    assert actual == KIT, (actual,KIT)
    checker = subprocess.check_output(['git','show',KIT+':Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n') == checker
    args.output.mkdir(parents=True,exist_ok=True)
    logs = args.output/'logs'
    logs.mkdir(exist_ok=True)
    records = []
    for stem,heads in LAYERS:
        module = stem if stem.startswith('Rule30') else 'Rule30Normalization'+stem+'Research'
        source = HERE/(module+'.lean')
        target = project/source.name
        report_path = args.output/(module+'.json')
        retained = None
        if args.resume and report_path.exists():
            old = json.loads(report_path.read_text(encoding='utf-8'))
            assert old['source_sha256']==sha(source.read_bytes())
            assert old['kit_commit']==KIT and old['checker_sha256']==sha(checker)
            assert old['check']['verdict']=='pass' and old['check']['replay']['ok']
            assert not old['check']['newAxioms'] and all(h['ok'] for h in old['check']['headlines'])
            assert target.read_bytes()==source.read_bytes()
            assert (project/'.lake/build/lib/lean'/(module+'.olean')).exists()
            retained = old
        if retained:
            records.append({'module':module,'source_sha256':retained['source_sha256'],
                            'constants':retained['check']['replay']['constants'],'headlines':heads,
                            'compile_seconds':retained['compile_seconds'],
                            'replay_seconds':retained['replay_seconds']})
            print(json.dumps({'module':module,'stage':'retained_exact_source_pass'}),flush=True)
            continue
        if target.exists() and target.read_bytes().replace(b'\r\n',b'\n') != source.read_bytes():
            if not args.replace_research_sources:
                raise RuntimeError('Different research source exists; inspect before replacing: '+str(target))
        shutil.copyfile(source,target)
        artifact = project/'.lake/build/lib/lean'/(module+'.olean')
        artifact.parent.mkdir(parents=True,exist_ok=True)
        print(json.dumps({'module':module,'stage':'compile'}),flush=True)
        compile_seconds = guarded([args.lake,'env','lean','-o',str(artifact),str(target)],
                                  project,logs/(module+'.compile.log'))
        argv = [args.lake,'env','lean','--run','Check.lean',module,'--claim','partial']
        for head in heads:
            argv += ['--headline',NS+head]
        print(json.dumps({'module':module,'stage':'full_kernel_replay'}),flush=True)
        log = logs/(module+'.check.log')
        seconds = guarded(argv,project,log)
        checked = json.loads([s for s in log.read_text(encoding='utf-8').splitlines()
                              if s.startswith('{')][-1])
        assert checked['verdict']=='pass' and checked['replay']['ok']
        assert not checked['newAxioms'] and all(h['ok'] for h in checked['headlines'])
        record = {'module':module,'source_sha256':sha(source.read_bytes()),
                  'kit_commit':KIT,'checker_sha256':sha(checker),'checker_unchanged':True,
                  'compile_seconds':compile_seconds,'replay_seconds':seconds,
                  'numeric_normalizer_equivalence_proved':False,
                  'infinite_trace_completeness_proved':False,'full_problem_solved':False,
                  'check':checked}
        report_path.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
        records.append({'module':module,'source_sha256':record['source_sha256'],
                        'constants':checked['replay']['constants'],'headlines':heads,
                        'compile_seconds':compile_seconds,'replay_seconds':seconds})
        print(json.dumps({'module':module,'stage':'pass',
                          'constants':checked['replay']['constants']}),flush=True)
    manifest = {'verdict':'pass','kit_commit':KIT,'checker_unchanged':True,
                'checker_sha256':sha(checker),'modules':records,
                'all_size_actual_row_stripe_implication_proved':True,
                'all_finite_times_early_stripe_meeting_proved':True,
                'stripe_relation_preserved_every_two_steps_proved':True,
                'stripe_relation_implies_equal_entire_center_trace_proved':True,
                'numeric_normalizer_equivalence_proved':False,
                'infinite_trace_completeness_proved':False,'full_problem_solved':False}
    (args.output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',
                                           encoding='utf-8',newline='\n')

if __name__=='__main__':
    main()
