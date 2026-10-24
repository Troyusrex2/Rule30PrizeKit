"""Replay selected public profile proofs, with precise upstream credit.

Adds only an import of the unchanged official statement kit. Proof bodies
are byte-preserved (apart from line endings). This is our independent audit,
not an official reviewer verdict or a new proof attributed to us.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import urllib.request

import audit_contributions as audit

REPOSITORY = 'ghywel/placego'
REVISION = '61fd612bb2c6f8fdd3a5667d5a8885d45f97195f'
ITEMS = {
    'RootedReturn': ['step_injective', 'child_unique', 'child_exists', 'rooted_walk_returns'],
    'ParityMask': ['diff_eq_cases', 'parity_compl', 'at_most_one_pred', 'diff_even', 'odd_driver_no_pred'],
    'JenPow2': ['jen_pow2', 'run_bound', 'run_bound_gcd', 'lemma_B2_quant', 'lemma_B2',
                'infinitely_many_white', 'no_adjacent_white', 'white_then_black', 'infinitely_many_black'],
    'BlackLock': ['lock9', 'lock_persists'],
}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project', type=Path, required=True)
    ap.add_argument('--lake', required=True)
    ap.add_argument('--module', choices=list(ITEMS), action='append')
    args = ap.parse_args()
    project = args.project.resolve()
    expected = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == expected
    evidence = audit.HERE/'external-profile-audit'
    evidence.mkdir(exist_ok=True)
    path = evidence/'report.json'
    report = json.loads(path.read_text()) if path.exists() else {
        'repository': REPOSITORY, 'head_commit': REVISION,
        'upstream_credit': 'ghywel/placego public research; Lean files credit Local (2026-10-09)',
        'pinned_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip(),
        'checker_modified': False, 'proof_bodies_unchanged': True,
        'adaptation': 'replace umbrella Mathlib import by selected Mathlib imports and official Rule30Prize; normalize line endings only',
        'official_review_status_claimed': False, 'full_problem_claim': False, 'modules': []}
    assert report['head_commit'] == REVISION
    for name in args.module or list(ITEMS):
        url = 'https://raw.githubusercontent.com/'+REPOSITORY+'/'+REVISION+'/tests/probes/lean/'+name+'.lean'
        raw = urllib.request.urlopen(url, timeout=30).read()
        imports = ('import Ruliology.CellularAutomata.Rule30Prize\n'
                   'import Mathlib.Data.ZMod.Basic\n'
                   'import Mathlib.Data.Fintype.Pigeonhole\n'
                   'import Mathlib.Algebra.BigOperators.Group.Finset.Basic\n'
                   'import Mathlib.Tactic.Choose\n'
                   'import Mathlib.Tactic.Push\n'
                   'import Mathlib.Tactic.Ring\n'
                   'import Mathlib.Tactic.LinearCombination\n'
                   'import Mathlib.Tactic.NormNum\n')
        body = raw.decode('utf-8').replace('\r\n', '\n')
        assert body.startswith('import Mathlib\n')
        old_source = imports+body[len('import Mathlib\n'):]
        if name == 'JenPow2':
            imports += 'import Mathlib.Tactic.Linarith\n'
        source = imports+body[len('import Mathlib\n'):]
        module = 'Rule30External'+name+'NarrowReview'
        target = project/(module+'.lean')
        if target.exists() and target.read_text(encoding='utf-8') != source:
            if (name != 'JenPow2' or target.read_text(encoding='utf-8') != old_source
                    or (project/'.lake/build/lib/lean'/(module+'.olean')).exists()):
                raise RuntimeError('Refusing to overwrite different review source')
        target.write_text(source, encoding='utf-8', newline='\n')
        artifact = project/'.lake/build/lib/lean'/(module+'.olean')
        compile_seconds = audit.run([args.lake, 'env', 'lean', '-o', str(artifact), str(target)],
                                    project, evidence/(name+'-build.log'), timeout=300)
        argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
        for h in ITEMS[name]:
            argv += ['--headline', name+'.'+h]
        log = evidence/(name+'-check.log')
        replay_seconds = audit.run(argv, project, log, timeout=300)
        data = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
        assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
        assert all(h['ok'] for h in data['headlines'])
        item = {'module': name, 'source_url': url, 'source_sha256': hashlib.sha256(raw).hexdigest(),
                'adapted_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                'compile_seconds': round(compile_seconds, 3), 'replay_seconds': round(replay_seconds, 3),
                'check': data}
        report['modules'] = [i for i in report['modules'] if i['module'] != name]+[item]
        path.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
        print(json.dumps({'module': name, 'verdict': 'pass', 'constants': data['replay']['constants']}), flush=True)
    report.update(verdict='pass', audited_modules=len(report['modules']),
                  replayed_constants=sum(m['check']['replay']['constants'] for m in report['modules']),
                  selected_concrete_headlines=sum(len(m['check']['headlines']) for m in report['modules']),
                  generic_theorems='Fully replayed; universe-polymorphic generic theorems are not selected as headlines')
    path.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
