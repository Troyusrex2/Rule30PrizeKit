"""Replay Keith Adler's constant-window proof in the unchanged pinned kit.

The proof is an independent formalization of a known period-one result,
credited upstream to D. L. Condrey. This script makes no novelty/prize claim.
The upstream Apache-2.0 copyright header is preserved in the generated file.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from urllib.request import urlopen


COMMIT = 'ce8ed7df906f272bc9b606cde7a84b17b35eac4c'
URL = f'https://raw.githubusercontent.com/keithadler/rule30-constant-column-lean/{COMMIT}/ConstColumn.lean'
SHA = '6440117b2b5afd8318c5ed8abb5397c5b069335de94e03b7bfd969e4dbe76370'
PINNED = 'cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554'
BRIDGE = r'''
theorem evo_eq_evol (x : Int -> Bool) : forall t p,
    evo x t p = Ruliology.CellularAutomata.Rule30Realization.evol x t p
  | 0, _ => rfl
  | t+1, p => by
      change xor (evo x t (p-1)) (evo x t p || evo x t (p+1)) =
        xor (Ruliology.CellularAutomata.Rule30Realization.evol x t (p-1))
          (Ruliology.CellularAutomata.Rule30Realization.evol x t p ||
            Ruliology.CellularAutomata.Rule30Realization.evol x t (p+1))
      rw [evo_eq_evol x t (p-1),evo_eq_evol x t p,evo_eq_evol x t (p+1)]

theorem official_no_const_column (x : Int -> Bool) (A : Nat)
    (hz : forall i : Int, i < -(A : Int) \/ (A : Int) < i -> x i = false)
    (hne : exists i, x i = true) (c : Bool)
    (hc : forall t, t <= A+2 ->
      Ruliology.CellularAutomata.Rule30Realization.evol x t 0 = c) : False := by
  apply no_const_column x A hz hne c
  intro t ht
  rw [evo_eq_evol]
  exact hc t ht
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--lake', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--module', default='Rule30AdlerExternalAudit')
    args = parser.parse_args()
    project = args.project.resolve()
    assert re.fullmatch('[A-Za-z][A-Za-z0-9_]*', args.module)
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip()
    assert head == PINNED, 'This audit targets the recorded pinned reference checkout'
    checker = (project/'Check.lean').read_bytes()
    assert checker.replace(b'\r\n', b'\n') == subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    with urlopen(URL, timeout=30) as response:
        original = response.read()
    assert hashlib.sha256(original).hexdigest() == SHA
    source = ('import Ruliology.CellularAutomata.Rule30FiniteConfigs\n\nnamespace '+args.module+
              '\n\n'+original.decode('utf-8')+'\n'+BRIDGE+'\nend '+args.module+'\n')
    target = project/(args.module+'.lean')
    if target.exists():
        assert target.read_text(encoding='utf-8') == source, 'Refusing to overwrite different proof source'
    else:
        target.write_text(source, encoding='utf-8', newline='\n')
    args.output.mkdir(parents=True, exist_ok=True)
    artifact = project/'.lake/build/lib/lean'/(args.module+'.olean')
    built = subprocess.run([args.lake, 'env', 'lean', str(target), '-o', str(artifact)],
                           cwd=project, capture_output=True, text=True, encoding='utf-8', timeout=120)
    (args.output/'build.log').write_text(built.stdout+built.stderr, encoding='utf-8')
    assert built.returncode == 0, built.stdout[-2000:]
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', args.module, '--claim', 'partial']
    for name in ['no_const_column', 'official_no_const_column']:
        argv += ['--headline', args.module+'.'+name]
    checked = subprocess.run(argv, cwd=project, capture_output=True, text=True, encoding='utf-8', timeout=120)
    (args.output/'check.log').write_text(checked.stdout+checked.stderr, encoding='utf-8')
    assert checked.returncode == 0, checked.stdout[-2000:]
    data = json.loads([s for s in checked.stdout.splitlines() if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    assert (project/'Check.lean').read_bytes() == checker
    report = {'upstream_repository': 'keithadler/rule30-constant-column-lean',
              'upstream_commit': COMMIT, 'upstream_file': 'ConstColumn.lean',
              'upstream_source_sha256': SHA, 'pinned_project_commit': head,
              'author_credit': 'Keith Adler with Claude; prior mathematical result credited upstream to D. L. Condrey',
              'new_result_claim': False, 'full_problem_claim': False, 'checker_modified': False,
              'scope': 'Constant trace through times 0..A+2 impossible for a nonzero row supported in [-A,A]; includes equality to official evolution',
              'adaptation': 'Official import, enclosing namespace, and two additional bridge theorems; original upstream source preserved',
              'adapted_source_sha256': hashlib.sha256(target.read_bytes()).hexdigest(), 'check': data}
    (args.output/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'verdict': 'pass', 'constants': data['replay']['constants'],
                      'headlines': len(data['headlines'])}), flush=True)


if __name__ == '__main__':
    main()
