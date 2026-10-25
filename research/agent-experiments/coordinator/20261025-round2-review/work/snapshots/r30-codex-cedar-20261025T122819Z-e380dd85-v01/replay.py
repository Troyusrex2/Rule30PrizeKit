"""Compile only needed pinned catalog modules, then replay all custom declarations.
Invoked through guard.py. No shared build directories and no package downloads.
"""
import argparse,hashlib,json,os,shutil,subprocess,sys,time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PROJECT=ROOT.parents[1]/'cedar-round2-20261025-verifier'
LEAN=ROOT.parents[1]/'toolchain/lean-4.35.0-windows/bin/lean.exe'
PIN='3eca23c0a9fa6b153313655e6d51835406c2d06e'
CHECKER='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
EVIDENCE=ROOT/'evidence'
BUILD=PROJECT/'cedar-build'

def digest(data):return hashlib.sha256(data).hexdigest()
def command(args,env,log):
    started=time.monotonic()
    p=subprocess.run(args,cwd=PROJECT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log.write_bytes(p.stdout)
    if p.returncode:
        print(p.stdout.decode('utf-8',errors='replace')[-10000:])
        raise RuntimeError(f'Failed: {args} (exit {p.returncode})')
    return {'command':list(map(str,args)),'seconds':time.monotonic()-started,'exit_code':p.returncode}

def main():
    global PROJECT,LEAN,BUILD
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,default=PROJECT,help='Separate checkout at the verifier pin')
    parser.add_argument('--lean',type=Path,default=LEAN,help='Lean 4.35.0 executable')
    args=parser.parse_args()
    PROJECT=args.project.resolve();LEAN=args.lean.resolve();BUILD=PROJECT/'cedar-build'
    actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip()
    assert actual==PIN,(actual,PIN)
    assert subprocess.check_output([str(LEAN),'-V'],text=True).strip()=='4.35.0'
    pinned_checker=subprocess.check_output(['git','show',PIN+':Check.lean'],cwd=PROJECT)
    assert digest(pinned_checker)==CHECKER
    checker=(PROJECT/'Check.lean').read_bytes().replace(b'\r\n',b'\n')
    assert checker==pinned_checker
    BUILD.mkdir(exist_ok=True)
    environment=dict(os.environ,LEAN_PATH=str(BUILD),PYTHONDONTWRITEBYTECODE='1')
    steps=[];sources=[]
    # These modules import only Init and earlier members of this list.
    for stem in ('Rule30Jen','Rule30Prize','Rule30Realization'):
        relative=Path('Ruliology/CellularAutomata')/(stem+'.lean')
        source=PROJECT/'lean'/relative
        pinned=subprocess.check_output(['git','show',PIN+':lean/'+relative.as_posix()],cwd=PROJECT)
        assert source.read_bytes().replace(b'\r\n',b'\n')==pinned
        output=(BUILD/relative).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
        steps.append(command([str(LEAN),'--root='+str(PROJECT/'lean'),'-o',str(output),str(source)],environment,EVIDENCE/(stem+'.compile.log')))
        sources.append({'module':'Ruliology.CellularAutomata.'+stem,'pinned_source_sha256':digest(pinned)})
    custom=ROOT/'CedarAncestry.lean'
    target=PROJECT/custom.name
    shutil.copyfile(custom,target)
    steps.append(command([str(LEAN),'--root='+str(PROJECT),'-o',str(BUILD/'CedarAncestry.olean'),str(target)],environment,EVIDENCE/'CedarAncestry.compile.log'))
    heads=['rule30_normalizes','rule210_normalizes','parent_monotone','ancestor_monotone','ancestor_valid',
           'parent_valid30','parent_valid210','rule30_ancestry','seed_shift_evolves','canonical_ancestry',
           'rule210_ancestry','rule210_coupled_center_agrees']
    args=[str(LEAN),'--run',str(PROJECT/'Check.lean'),'CedarAncestry','--claim','partial']
    for head in heads:args+=['--headline','CedarAncestry.'+head]
    steps.append(command(args,environment,EVIDENCE/'CedarAncestry.check.log'))
    lines=(EVIDENCE/'CedarAncestry.check.log').read_text(encoding='utf-8').splitlines()
    checked=json.loads(next(s for s in reversed(lines) if s.startswith('{')))
    assert checked['verdict']=='pass' and checked['replay']['ok']
    assert not checked['newAxioms'] and all(h['ok'] for h in checked['headlines'])
    report={'kit_commit':PIN,'lean_version':'4.35.0','checker_sha256':CHECKER,'checker_unchanged':True,
            'module':'CedarAncestry','source_sha256':digest(custom.read_bytes()),'catalog_sources':sources,
            'commands':steps,'headlines':['CedarAncestry.'+x for x in heads],'check':checked,
            'full_problem_solved':False,'center_reach_lemma_proved':False,
            'path_pairing_involution_formalized':False,
            'formal_scope':'Local cancellation certificates; all-time conditional ancestry and monotone root order; Rule210 center countercontrol.'}
    (EVIDENCE/'kernel_report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'verdict':checked['verdict'],'replay':checked['replay'],'headlines':heads}))

if __name__=='__main__':main()
