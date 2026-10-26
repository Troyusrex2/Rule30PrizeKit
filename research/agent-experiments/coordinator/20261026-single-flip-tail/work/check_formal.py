from pathlib import Path
import hashlib,json,os,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
OWNER=Path.home()/'Rule30-offload'
assert OWNER.resolve() in ROOT.resolve().parents
project=OWNER/'research/notebook-offload-20261026/notebook/project'
lean=OWNER/'_cache/payload/toolchain/bin/lean.exe'
checker=project/'Check.lean'
expected='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==expected
module=sys.argv[1]
HEADS={'Rule30Slip94Research':['stream_golden','theta_periodic_28','golden_stream_charge_three_false'],
       'Rule30MaskedDefectResearch':['white_gate','second_left_difference','periodic_center_white_defects']}
HEADS.update({'Rule30VerifiedCoupledGoldenExtract':['u_golden','col1_drvRow','u_black_among_five','Psi_free_no00_no11111'], 'Rule30CoupledSixWordResearch':['six_check','no_u_101001','psi_free_no010110'], 'Rule30SingleSlipExclusionResearch':['singleSlip_word','no_right_half_single_slip','slip94_not_realizable']})
if module == 'Rule30VerifiedCoupledGoldenExtract':
    namespace='Rule30Submission'
else:
    namespace=module
HEADS['Rule30CommonPastResearch']=['mode_periodic','common_past_lift','common_subset_past_lift','finite_common_past_lift','actual_recombination','physical_mode','vacuum_pulse_no_finite_past']
HEADS['Rule30ColumnReaderResearch']=['acceptance_invariant','prefix_step','reader_sound']
HEADS['Rule30ReaderSeparationResearch']=['state_step','state_period_two','sink_time_iff','nonsink_word','reader_complete_outside_sink','nonsink_two_times']
HEADS['Rule30LateSeparationResearch']=['example_length','example_sink','example_first_difference']
HEADS['Rule30SharedTailCounterResearch']=['frame_step','full_period_eight','shared_tail','heads_equal','source_opposite','common_neighbor_nonconstant','initial_difference_finite','initial_infinite','shared_tail_resynchronization']
HEADS['Rule30SharedTailDelayResearch']=['orbit_local','tail_stays_shared','source_stays_opposite','arbitrary_finite_delay','no_background_independent_bound']
HEADS['Rule30SinkDelayResearch']=['original_word_sink','arbitrary_sink_delay']
HEADS['Rule30SingleFlipTailResearch']=['frame_step','period_eight','single_initial_flip','initial_true_formula','initial_false_formula','source_opposite','heads_equal','head_not_period_two','common_OR','OR_nonconstant','neighbors_differ','initial_infinite','single_flip_invisible','arbitrary_finite_single_flip_delay']
assert module in HEADS
src=ROOT/(module+'.lean');target=project/src.name
target.write_bytes(src.read_bytes())
out=ROOT/'formal'/module;out.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,LEAN_PATH=str(project/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
heads=[namespace+'.'+h for h in HEADS[module]]
commands=[('build',[str(lean),'-o',str(project/'.lake/build/lib/lean'/(module+'.olean')),target.name]),
          ('check',[str(lean),'--run',str(checker),module,'--claim','partial']+
           sum((['--headline',h] for h in heads),[]))]
stages=[]
for stage,argv in commands:
 start=time.monotonic()
 with (out/(stage+'.log')).open('wb') as log:
  r=subprocess.run(argv,cwd=project,env=env,stdout=log,stderr=subprocess.STDOUT)
 stages.append({'stage':stage,'seconds':round(time.monotonic()-start,3),'exit_code':r.returncode})
 if r.returncode:print((out/(stage+'.log')).read_text(encoding='utf-8',errors='replace')[-9000:],flush=True)
 r.check_returncode()
checked=json.loads(next(line for line in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if line.startswith('{')))
assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
assert all(h['ok'] for h in checked['headlines'])
assert hashlib.sha256(checker.read_bytes()).hexdigest()==expected
report={'passed':True,'machine':'G913','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
        'kit_commit':'0090056412733accaa27643d3cbbf982104f2251','checker_sha256':expected,
        'checker_unchanged':True,'stages':stages,'check':checked,'full_problem_solved':False}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':True,'module':module,'replay':checked['replay'],'source_sha256':report['source_sha256']}),flush=True)
