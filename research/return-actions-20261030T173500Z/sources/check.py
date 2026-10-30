from pathlib import Path
import os,subprocess,shutil,json,hashlib,time
R=Path(__file__).resolve().parent;P=R/'project'
shutil.copyfile(R/'StatementGuard.lean',P/'StatementGuard.lean')
lean=Path('D:/MWB/Rule30/toolchain/lean-4.35.0-windows/bin/lean.exe')
env=dict(os.environ,LEAN_PATH=str(P),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
start=time.monotonic()
def run(args,name):
    with (R/name).open('wb') as f:
        r=subprocess.run(list(map(str,args)),cwd=P,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=60)
    if r.returncode:
        print((R/name).read_text(encoding='utf-8',errors='replace')[-4500:]);raise SystemExit(r.returncode)
run([lean,'-o',P/'StatementGuard.olean',P/'StatementGuard.lean'],'guard.log')
args=[lean,'--run',P/'Check.lean','ReturnActions','--claim','partial']
for h in ['prefix_period','dyadic_factorization','shared_return_confines','rigidity_iff_return_injective','canonical_iff_return_injective']:
    args+=['--headline','ReturnActions.'+h]
run(args,'checker.log')
result=json.loads(next(x for x in reversed((R/'checker.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
assert result['verdict']=='pass' and result['replay']['ok'] and not result['newAxioms']
assert all(h['ok'] and h['typeMatches'] for h in result['headlines'])
out=dict(passed=True,checker=result,seconds=round(time.monotonic()-start,3),
    checker_sha256=hashlib.sha256((P/'Check.lean').read_bytes()).hexdigest(),
    source_warnings='warning:' in (R/'ReturnActions.log').read_text(encoding='utf-8'),
    scope='Every infinite code has dyadic prefix returns. OPEN same-edge rigidity is equivalent to OPEN injectivity of the actual dyadic return-tail functions on black-edge prefixes. Shared functional returns imply confinement for every P>0.',
    prize_solved=False)
(R/'CHECK.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(passed=True,replay=result['replay'],headlines=len(result['headlines']),new_axioms=result['newAxioms'])))
