"""Fresh core-only replay. Requires only Python and the recorded Lean toolchain."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, time

p = argparse.ArgumentParser()
p.add_argument('--lean', required=True)
p.add_argument('--out', required=True)
a = p.parse_args()
here = Path(__file__).resolve().parent
out = Path(a.out).resolve()
out.mkdir(parents=True, exist_ok=False)
src = out / 'sources'
shutil.copytree(here / 'sources', src)
logs = out / 'logs'
logs.mkdir()
env = dict(os.environ, LEAN_PATH=str(src), LEAN_NUM_THREADS='1')
start = time.monotonic()
runs = []
prefix = 'Ruliology.CellularAutomata.Rule30GroupCocycle.'
headlines = ['full_background_connection', 'background_gauge_all_groups',
             'cyclic_products_background', 'boolean_flux_coboundary']

def run(name, args):
    t = time.monotonic()
    r = subprocess.run([a.lean] + args, cwd=src, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    (logs / (name + '.log')).write_bytes(r.stdout)
    row = dict(name=name, exit=r.returncode, seconds=round(time.monotonic()-t, 3))
    runs.append(row)
    print(json.dumps(row), flush=True)
    if r.returncode:
        raise RuntimeError('Check failed; see ' + str(logs / (name + '.log')))
    if not name.startswith('Check') and r.stdout.strip():
        raise RuntimeError('Owned-source build was not clean; inspect saved log')
    if time.monotonic()-start > 120:
        raise TimeoutError('Overall 120-second guard')

for name in ['Rule30Jen', 'Rule30Prize', 'Rule30GroupCocycle','Rule30BoundaryProfileCounterexample']:
    f = 'Ruliology/CellularAutomata/' + name
    run(name, ['-o', f + '.olean', f + '.lean'])
run('StatementGuard', ['-o', 'StatementGuard.olean', 'StatementGuard.lean'])
args = ['--run', 'Check.lean', prefix[:-1], '--claim', 'partial']
for h in headlines:
    args += ['--headline', prefix+h]
run('Check', args)
counter_args=['--run','Check.lean','Ruliology.CellularAutomata.Rule30BoundaryProfileCounterexample','--claim','partial']
for h in ['two_infinite_pasts_same_nonalt_final','recurrence','no_white_profile']:
    counter_args+=['--headline','Ruliology.CellularAutomata.Rule30BoundaryProfileCounterexample.'+h]
run('CheckBoundary',counter_args)
boundary=json.loads(next(x for x in (logs/'CheckBoundary.log').read_text(encoding='utf-8').splitlines() if x.startswith('{')))
assert boundary['verdict']=='pass' and boundary['newAxioms']==[]
assert all(x['ok'] for x in boundary['headlines'])
assert all(x['standardAxioms'] for x in boundary['declared'])
lines = (logs / 'Check.log').read_text(encoding='utf-8').splitlines()
check = json.loads(next(x for x in lines if x.startswith('{')))
assert check['verdict'] == 'pass' and check['replay']['ok']
assert check['newAxioms'] == [] and check['verifiedTargets'] == []
assert all(x['ok'] for x in check['headlines'])
assert all(x['standardAxioms'] for x in check['declared'])
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
record = dict(runs=runs, seconds=round(time.monotonic()-start, 3),
              lean_sha256=sha(Path(a.lean)), checker_sha256=sha(src/'Check.lean'),
              input_sha256={f.relative_to(src).as_posix():sha(f)
                            for f in sorted(src.rglob('*.lean'))},
              replay=check['replay'], headlines=check['headlines'], boundary_replay=boundary['replay'], boundary_headlines=boundary['headlines'],
              new_axioms=check['newAxioms'], prize_claim=False,
              mathlib_on_build_path=False, owned_objects_reused=False)
(out/'RESULT.json').write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
print('PASS: fresh closure, explicit statements, unchanged kernel replay', flush=True)
