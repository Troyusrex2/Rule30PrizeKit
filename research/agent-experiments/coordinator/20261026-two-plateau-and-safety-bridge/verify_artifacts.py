"""Byte, provenance and scope audit; does not substitute for kernel replay."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--staged', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent
repo = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], cwd=root, text=True).strip())
prefix = root.relative_to(repo).as_posix()
def read(name):
    return subprocess.check_output(['git', 'show', ':' + prefix + '/' + name], cwd=repo) if args.staged else (root / name).read_bytes()
def data(name):
    return json.loads(read(name))
def sha(value):
    return hashlib.sha256(value).hexdigest()

files = data('artifacts.json')['files']
for name, digest in files.items():
    assert sha(read(name)) == digest, name
pin = '5473ffd075f63c9d626e63b8455805d4831b39ca'
checker = 'b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert sha(subprocess.check_output(['git', 'show', pin + ':Check.lean'], cwd=repo)) == checker
assert data('work/public-refresh/environment.json')['kit']['commit'] == pin
summary = data('summary.json')
provenance = data('provenance.json')
batch = data('work/formal/cedar-bridge-batch.json')
assert batch['passed'] and batch['pin'] == pin and batch['checker_sha256'] == checker
expected = {
    'Rule30SaturatedOrPeriodResearch': 8,
    'Rule30PlateauPairCertificate': 122,
    'Rule30TwoPlateauRigidityResearch': 48,
    'CedarSafetySoundness': 137,
    'CedarSafetySemantics': 75,
    'CedarSafetyBridge': 8,
    'CedarWhiteTransport': 18,
}
for module, count in expected.items():
    report = data('work/formal/' + module + '/report.json')
    source = read('work/' + module + '.lean')
    assert report['source_sha256'] == sha(source), module
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel', source, re.M), module
    result = report['checker']
    assert result['module'] == module and result['verdict'] == 'pass'
    assert result['replay'] == {'constants': count, 'ok': True}
    assert not result['newAxioms'] and result['importsStatements']
    assert result['headlines'] and all(h['ok'] and h['typeMatches'] for h in result['headlines'])
    assert result['claim'] == 'partial' and not result['verifiedTargets']
    if module.startswith('Rule30'):
        assert report['passed'] and report['pin'] == pin and report['checker_sha256'] == checker
    elif module == 'CedarSafetySoundness':
        assert report['passed'] and report['pin'] == pin and not report['reference_cache_reused']
        for name, digest in report['official_source_hashes'].items():
            assert sha(subprocess.check_output(['git', 'show', pin + ':' + name], cwd=repo)) == digest
        assert all(x['exit'] == 0 for x in report['fresh_dependency_builds'])
    else:
        assert report == next(x for x in batch['new_modules'] if x['module'] == module)
    if module.startswith('Cedar'):
        assert sha(source) == provenance['cedar_module_hashes'][module]
for dep in provenance['dependencies']:
    source = read('work/dependencies/' + dep['module'] + '.lean')
    assert sha(source) == dep['sha256'] and source == (repo / dep['source']).read_bytes()
assert provenance['cedar_full_response_hash_audits'] == [152, 140]
for name in files:
    if name.startswith('work/evidence/') and name.endswith('.guard.json'):
        guard = data(name)
        assert guard['exit_code'] == 0 and guard['guard_stop'] is None, name
        assert guard['limits'] == {'seconds': 300, 'owned_rss_gib': 8, 'minimum_system_available_gib': 2}
        assert guard['elapsed_seconds'] <= 300
        assert guard['peak_owned_rss_bytes'] <= 8 * 1024**3
        assert guard['minimum_system_available_bytes'] >= 2 * 1024**3
certificate = data('work/plateau-certificate.json')
assert certificate['level_counts'] == [576, 152, 92, 70]
assert len(certificate['live_states']) == 70 and certificate['projection_count'] == 16
assert certificate['projected_even_reach_pairs'] == 366 and certificate['all_projected_swaps_excluded']
assert certificate['literal_row_edges_audited'] == 256
driver = data('work/periodic-driver-witness-audit.json')['independent_literal_audit']
assert [x['scalar_edges_checked'] for x in driver] == [57, 100, 48]
assert all(x['common_base_verified'] and x['noncommuting_output_words_verified'] for x in driver)
double = data('work/double-clock-independent-audit.json')
assert double['finite_white_R2_control_passed'] and double['no_genuine_white_counterexample_claim']
assert len(double['results']) == 8
assert all(x['all_literal_and_clock_constraints_passed'] and x['genuine_white_equation_failures'] > 0 for x in double['results'])
assert summary['our_new_modules'] | summary['cedar_replayed_modules'] == expected
assert summary['our_uniform_two_plateau_exclusion_proved']
assert summary['cedar_conditional_safety_language_equivalence_proved']
for claim in ['safety_completeness_proved', 'physical_center_bridge_proved', 'full_problem_solved',
              'new_prize_submission', 'new_pull_request', 'Wolfram_backend_verification_claimed']:
    assert not summary[claim], claim
count = archives = 0
for manifest in root.parent.glob('*/artifacts.json'):
    if manifest.parent.name in {root.name, '20261024-seven', '20261025-round2', '20261025-round2-review'}:
        continue
    old = json.loads(manifest.read_bytes())['files']
    for name, digest in old.items():
        assert sha((manifest.parent / name).read_bytes()) == digest, (manifest.parent.name, name)
    count += len(old)
    archives += 1
assert (count, archives) == (3188, 38)
for name in files:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]', read(name), re.I), name
print(json.dumps({'passed': True, 'staged': args.staged, 'selected_hashes': len(files),
                  'fully_replayed_constants': sum(expected.values()), 'prior_hashes_unchanged': count,
                  'prior_archives_unchanged': archives, 'full_problem_solved': False}))
