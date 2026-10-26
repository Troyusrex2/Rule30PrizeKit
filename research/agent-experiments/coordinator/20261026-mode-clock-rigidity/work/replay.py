from pathlib import Path
import hashlib,json,os,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
OWNER=Path.home()/'Rule30-offload'
assert OWNER.resolve() in ROOT.resolve().parents
project=OWNER/'research/verifier9-20261026/project'
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
HEADS['Rule30FrontReductionResearch']=['first_source','suffix_mode','preservation_iff_front','clock_no_flips','period_two_source_stable','preservation_of_collision_clock']
HEADS['Rule30ReaderCollisionBridgeResearch']=['non16_permanent','sixteen_clock','accepted_collision_clock','reader_exact_of_sink_separation','collision_clock_of_sink_separation','front_of_sink_separation','preservation_of_sink_separation']
HEADS['Rule30ColumnReaderResearch']=['acceptance_invariant','prefix_step','reader_sound']
HEADS['Rule30ReaderSeparationResearch']=['state_step','state_period_two','sink_time_iff','nonsink_word','reader_complete_outside_sink','nonsink_two_times']
HEADS['Rule30ReaderEquivalenceResearch']=['related_refl','related_symm','related_trans','shared_representative','related_sound']
HEADS['Rule30ReaderCanonicalResearch']=['canonical_exists','canonical_unique','canonical_step','same_iff_normal_eq','normal_step','canonical_completeness_reduction','canonical_count']
HEADS['Rule30OrClockObserverResearch']=['shift_flag','older_recovered','hidden_difference_impossible','or_pair_injective_of_anti','actual_or_clock_observer','plateau_local_counterexample']
HEADS['Rule30ReaderObserverReductionResearch']=['extension_words','same_snoc','parent_observer_iff','parent_bit_complete_reduction']
HEADS['Rule30ClockJetResearch']=['shift_difference_step','shift_or_mask','shift_or_difference','plateau_or_double','actual_plateau_jet']
HEADS['Rule30CubicWitnessData']=['check_orbit_sample','check_moment_sample','check_target']
HEADS['Rule30CubicPackedBench']=['check_orbit_sample','check_moment_sample','check_target']
HEADS['Rule30CubicPackedFast']=['check_orbit_sample','check_moment_sample','check_target']
HEADS['Rule30CubicCertificateData']=['data_size']
HEADS['Rule30CubicFullCheckBench']=['orbit_chunk', 'moment_chunk']
HEADS['Rule30CubicOrbitCheck00']=['checked']
HEADS['Rule30CubicOrbitCheck01']=['checked']
HEADS['Rule30CubicOrbitCheck02']=['checked']
HEADS['Rule30CubicOrbitCheck03']=['checked']
HEADS['Rule30CubicOrbitCheck04']=['checked']
HEADS['Rule30CubicOrbitCheck05']=['checked']
HEADS['Rule30CubicOrbitCheck06']=['checked']
HEADS['Rule30CubicOrbitCheck07']=['checked']
HEADS['Rule30CubicOrbitCheck08']=['checked']
HEADS['Rule30CubicOrbitCheck09']=['checked']
HEADS['Rule30CubicMomentCheck00']=['row0', 'row1', 'row2', 'row3']
HEADS['Rule30CubicMomentCheck01']=['row4', 'row5', 'row6', 'row7']
HEADS['Rule30CubicMomentCheck02']=['row8', 'row9', 'row10', 'row11']
HEADS['Rule30CubicMomentCheck03']=['row12', 'row13', 'row14', 'row15']
HEADS['Rule30CubicMomentCheck04']=['row16', 'row17', 'row18', 'row19']
HEADS['Rule30CubicMomentCheck05']=['row20', 'row21', 'row22', 'row23']
HEADS['Rule30CubicMomentCheck06']=['row24', 'row25', 'row26', 'row27']
HEADS['Rule30CubicMomentCheck07']=['row28', 'row29', 'row30', 'row31']
HEADS['Rule30CubicMomentCheck08']=['row32', 'row33', 'row34', 'row35']
HEADS['Rule30CubicMomentCheck09']=['row36', 'row37', 'row38', 'row39']
HEADS['Rule30CubicMomentCheck10']=['row40', 'row41', 'row42', 'row43']
HEADS['Rule30CubicMomentCheck11']=['row44', 'row45', 'row46', 'row47']
HEADS['Rule30CubicMomentCheck12']=['row48', 'row49', 'row50', 'row51']
HEADS['Rule30CubicMomentCheck13']=['row52', 'row53', 'row54', 'row55']
HEADS['Rule30CubicMomentCheck14']=['row56', 'row57', 'row58', 'row59']
HEADS['Rule30CubicMomentCheck15']=['row60', 'row61', 'row62', 'row63']
HEADS['Rule30CubicPackedSemantics']=['parity_semantics','word_getElem','packed_bit']
HEADS['Rule30CubicPackedSemanticsV2']=['parity_semantics','word_getElem','stepPacked_matches_rule']
HEADS['Rule30CubicOrbitSemantics']=['packed_iter', 'run_profile', 'checked_orbit_is_actual_cycle']
HEADS['Rule30CubicCertificateChecked']=['all_orbits_checked', 'all_moments_checked', 'target_checked', 'phase_count', 'every_record_is_canonical_cycle']
HEADS['Rule30CubicPhaseSemantics']=['canonical_last_free','all_certificate_phases_canonical','all_certificate_profiles_actual']
HEADS['Rule30CubicAlgebraResearch']=['head_triples_zero','head_polynomial_zero','no_cubic_head_decoder']
HEADS['Rule30ClockSearchResearch']=['scan_correct','scan_congr','anti_clock_window','actual_head_clock_window','decodeHead_congr']
HEADS['Rule30ClockModeResearch']=['lower_readout_eq','actual_lower_observer_data','older_recovered_of_modes_equal','lower_readout_parity','xsum_true_even']
HEADS['Rule30EvenModeRigidityResearch']=['constant_readout_driver','even_constant_mode_impossible','actual_even_plateau_readout','actual_even_plateau_or_no_half_period','constant_or_forces_double_period','actual_even_plateau_or_clock_rigidity']
HEADS['Rule30ModeClockRigidityResearch']=['mode_readout_no_half_clock','actual_lower_readout_no_half_clock']
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
        'kit_commit':'5473ffd075f63c9d626e63b8455805d4831b39ca','checker_sha256':expected,
        'checker_unchanged':True,'stages':stages,'check':checked,'full_problem_solved':False}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':True,'module':module,'replay':checked['replay'],'source_sha256':report['source_sha256']}),flush=True)
