"""Build the core catalog and replay every declaration in all nine new modules."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

import psutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREFIX = 'Ruliology.CellularAutomata.'
TARGETS = {
    'Rule30SpacingRenormalizationResearch': ['reconstruction_translate', 'support_transfer',
        'finite_transfer', 'transform_spaced_iff', 'periodFive_spaced',
        'transform_not_spaced', 'second_translation_fails'],
    'Rule30PackedReconstructionResearch': ['packed_sound'],
    'Rule30SpacingGapCounterexampleResearch': ['gate31_gaps', 'gate31_spaced',
        'seventeen_white', 'no_uniform_gap_bound_sixteen'],
    'Rule30DrivenPrefixResearch': ['packed_sound', 'double_prefix', 'iterate_mod_bit'],
    'Rule30Certificates.DrivenEmptyWall': ['good_all', 'entry'],
    'Rule30EmptyGateSpacingResearch': ['empty_windows', 'empty_spaced', 'empty_next_gap',
        'empty_black_after', 'empty_reconstruction_translate', 'transformed_empty_not_spaced'],
    'Rule30Certificates.DrivenEmptyCore': ['observe_trim', 'good_all', 'entry'],
    'Rule30EmptyGateLanguageResearch': ['refined_spaced', 'refined_next_gap',
        'no_successive_short_gaps', 'windowWord_allowed'],
    'Rule30ExactReturnResearch': ['exactReturn_iff_nearSpaced', 'translation_iff_nearSpaced',
        'transformed_exactReturn_iff', 'empty_gate_fails_arbitrarily_late',
        'empty_second_translation_fails', 'lastAllowed_transformed_return',
        'lastAllowed_transformed_not_spaced'],
}


def run(argv, cwd, log):
    began = time.monotonic()
    with log.open('w', encoding='utf-8', newline='\n') as out:
        proc = subprocess.Popen(argv, cwd=cwd, stdout=out, stderr=subprocess.STDOUT)
        task = psutil.Process(proc.pid)
        try:
            while proc.poll() is None:
                time.sleep(.5)
                try:
                    owned = [task] + task.children(recursive=True)
                except psutil.NoSuchProcess:
                    owned = []
                rss = 0
                for child in owned:
                    try:
                        rss += child.memory_info().rss
                    except psutil.NoSuchProcess:
                        pass
                if rss > 8*1024**3 or psutil.virtual_memory().available < 2*1024**3 or time.monotonic()-began > 1200:
                    raise RuntimeError('Owned verification job exceeded its resource guard; no pass claimed')
            if proc.returncode:
                raise RuntimeError(log.read_text(encoding='utf-8')[-2500:])
        finally:
            if proc.poll() is None:
                try:
                    owned = [task] + task.children(recursive=True)
                except psutil.NoSuchProcess:
                    owned = []
                for child in reversed(owned):
                    try:
                        child.kill()
                    except psutil.NoSuchProcess:
                        pass
                proc.wait()
    return round(time.monotonic()-began, 3)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lake', default='lake')
    args = ap.parse_args()
    evidence = HERE / 'evidence'
    evidence.mkdir(exist_ok=True)
    report = {'verdict': 'running', 'full_problem_claim': False,
              'period_two_excluded': False, 'CQ01Empty_proved': False,
              'example_gate31_finite_right_realizability_claim': False,
              'empty_right_gate_spacing_proved': True,
              'checker_modified': False, 'modules': []}
    target = HERE / 'catalog-verification.json'
    target.write_text(json.dumps(report)+'\n', encoding='utf-8', newline='\n')
    expected = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=ROOT)
    assert (ROOT/'Check.lean').read_bytes().replace(b'\r\n',b'\n') == expected
    root = (ROOT/'lean/Ruliology.lean').read_text(encoding='utf-8')
    for stem in TARGETS:
        if not stem.startswith('Rule30Certificates.'):
            assert 'public import '+PREFIX+stem in root
    report['core_build_seconds'] = run([args.lake, 'build', 'Ruliology'], ROOT/'lean', evidence/'core-build.log')
    report['standalone_core_catalog_build'] = True
    for stem, headlines in TARGETS.items():
        module = PREFIX + stem
        run([args.lake, 'build', module], ROOT, evidence/(stem+'.build.log'))
        argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
        for h in headlines:
            argv.extend(['--headline',module+'.'+h])
        log = evidence/(stem+'.check.log')
        run(argv, ROOT, log)
        data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines()
                           if s.startswith('{')][-1])
        assert data['verdict']=='pass' and data['replay']['ok'] and not data['newAxioms']
        assert all(h['ok'] for h in data['headlines'])
        source = ROOT/'lean/Ruliology/CellularAutomata'/Path(stem.replace('.','/')).with_suffix('.lean')
        report['modules'].append({'module':module,
            'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(), 'check':data})
        target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps({'module':module,'constants':data['replay']['constants'],'verdict':'pass'}),flush=True)
    report.update(verdict='pass', source_base_commit=subprocess.check_output(
        ['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        root_source_sha256=hashlib.sha256((ROOT/'lean/Ruliology.lean').read_bytes()).hexdigest())
    target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')


if __name__=='__main__':
    main()
