"""Build the standalone core catalog serially, then fully replay both modules."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

import psutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREFIX = 'Ruliology.CellularAutomata.'
TARGETS = {
    'Rule30ControlledResponseResearch': [
        'run_sound', 'responseEq_iff_runs', 'responseEq_all_prepend', 'responseEq_two',
        'sameResponse_iff_diagonal', 'sameResponse_iff_drv', 'tail_011_drv', 'tail_101_drv',
        'responseEq_iff_observationPrefix', 'short_window_agreement', 'short_window_not_sameResponse',
        'fixed_driver_counterexample', 'feedback_left_equal', 'tail_011_center', 'tail_101_center'],
    'Rule30PeriodicProfileCounterResearch': [
        'frame_step', 'iterate_frame', 'full_period_eight', 'same_OR', 'OR_nonconstant',
        'heads_differ', 'tail_OR_different', 'infinite_true', 'infinite_false', 'loss_frame_step',
        'loss_full_period_eight', 'loss_head_period_two', 'loss_full_period_lower_bound',
        'loss_not_head_period_one', 'loss_infinite']}


def run(argv, cwd, log):
    began = time.monotonic()
    with log.open('w', encoding='utf-8', newline='\n') as out:
        proc = subprocess.Popen(argv, cwd=cwd, stdout=out, stderr=subprocess.STDOUT)
        task = psutil.Process(proc.pid)
        try:
            while proc.poll() is None:
                time.sleep(.5)
                try: owned = [task]+task.children(recursive=True)
                except psutil.NoSuchProcess: owned = []
                rss = 0
                for child in owned:
                    try: rss += child.memory_info().rss
                    except psutil.NoSuchProcess: pass
                if rss > 8*1024**3 or psutil.virtual_memory().available < 2*1024**3 or time.monotonic()-began > 600:
                    raise RuntimeError('Owned verification job exceeded its resource guard; no pass claimed')
            if proc.returncode: raise RuntimeError(log.read_text(encoding='utf-8')[-3000:])
        finally:
            if proc.poll() is None:
                try: owned = [task]+task.children(recursive=True)
                except psutil.NoSuchProcess: owned = []
                for child in reversed(owned):
                    try: child.kill()
                    except psutil.NoSuchProcess: pass
                proc.wait()
    return round(time.monotonic()-began, 3)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lake', default='lake')
    args = ap.parse_args()
    evidence = HERE/'evidence'
    evidence.mkdir(exist_ok=True)
    target = HERE/'catalog-verification.json'
    expected = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=ROOT)
    assert (ROOT/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == expected
    project = ROOT/'lean'
    visited, order = set(), []

    def visit(module):
        if module in visited: return
        path = project/Path(module.replace('.', '/')).with_suffix('.lean')
        if not path.exists(): return
        visited.add(module)
        for dependency in re.findall(r'^(?:public )?import ([\w.]+)', path.read_text(encoding='utf-8'), re.MULTILINE):
            visit(dependency)
        order.append(module)

    visit('Ruliology')
    for stem in TARGETS: assert PREFIX+stem in visited
    report = {'verdict': 'running', 'full_problem_claim': False, 'finite_tail_completeness_proved': False,
        'period_two_excluded': False, 'checker_modified': False, 'core_build': [], 'modules': []}
    for module in order:
        seconds = run([args.lake, 'build', module], project, evidence/(module+'.build.log'))
        report['core_build'].append({'module': module, 'seconds': seconds})
        target.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
        print(json.dumps({'core_module': module, 'completed': len(report['core_build']), 'total': len(order)}), flush=True)
    report['standalone_core_catalog_build'] = True
    for stem, headlines in TARGETS.items():
        module = PREFIX+stem
        run([args.lake, 'build', module], ROOT, evidence/(stem+'.build.log'))
        argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
        for h in headlines: argv += ['--headline', module+'.'+h]
        log = evidence/(stem+'.check.log')
        run(argv, ROOT, log)
        data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
        assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
        assert all(h['ok'] for h in data['headlines'])
        path = ROOT/'lean/Ruliology/CellularAutomata'/(stem+'.lean')
        report['modules'].append({'module': module, 'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'check': data})
        print(json.dumps({'module': module, 'constants': data['replay']['constants'], 'verdict': 'pass'}), flush=True)
    report.update(verdict='pass', root_source_sha256=hashlib.sha256((project/'Ruliology.lean').read_bytes()).hexdigest(),
        source_base_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip())
    target.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
