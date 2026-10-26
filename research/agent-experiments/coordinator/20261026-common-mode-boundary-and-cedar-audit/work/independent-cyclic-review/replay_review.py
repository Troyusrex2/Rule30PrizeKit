"""Fresh pinned official kit build and full replay of the supplied 48-constant cyclic diagnostic."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,tarfile,time
ROOT=Path(__file__).resolve().parent
PIN='5473ffd075f63c9d626e63b8455805d4831b39ca'
CHECKER='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
ORDER=['Rule30CyclicSubsetObstructionResearch']
HEADS={}
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--kit-repo',type=Path,required=True);ap.add_argument('--lean',type=Path,required=True)
ap.add_argument('--out',type=Path,required=True);ap.add_argument('--published',type=Path,default=ROOT/'supplied')
a=ap.parse_args();out=a.out.resolve();repo=a.kit_repo.resolve();published=a.published.resolve();lean=a.lean.resolve()
assert not out.exists() and not out.is_relative_to(repo)
out.mkdir(parents=True);kit=out/'kit';kit.mkdir();logs=out/'logs';logs.mkdir();lib=kit/'private-lib';lib.mkdir()
commands=[];results=[];started=time.monotonic()
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def run(argv,label,cwd=kit,env=None):
    argv=[str(x) for x in argv];event=dict(command=argv,cwd=str(cwd),started=True)
    commands.append(event);(out/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
    log=logs/(label+'.log');begin=time.monotonic()
    try:
        with log.open('wb') as f:p=subprocess.run(argv,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=270)
        event.update(exit_code=p.returncode,seconds=time.monotonic()-begin,log=str(log));p.check_returncode()
    except BaseException as e:
        event.update(error=repr(e),seconds=time.monotonic()-begin,log=str(log));raise
    finally:(out/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
    return log
try:
    version=run([lean,'--version'],'version',out).read_text(encoding='utf-8').strip()
    assert 'version 4.35.0,' in version
    archive=out/'kit-source.tar'
    run(['git','-C',repo,'archive','--format=tar','--output',archive,PIN],'archive',out)
    with tarfile.open(archive) as tf:
        for member in tf.getmembers():
            target=(kit/member.name).resolve()
            assert target==kit or target.is_relative_to(kit)
            assert not member.issym() and not member.islnk()
        tf.extractall(kit,filter='data')
    official={p.relative_to(kit).as_posix():sha(p) for p in kit.rglob('*') if p.is_file()}
    assert official['Check.lean']==CHECKER
    assert (kit/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0'
    (out/'official-source-hashes.json').write_text(json.dumps(official,indent=2)+'\n')
    custom={}
    for module in ORDER:
        source=next(p for p in [published/(module+'.lean')] if p.is_file())
        target=kit/(module+'.lean');target.write_bytes(source.read_bytes());custom[module]=sha(target)
    assert custom['Rule30CyclicSubsetObstructionResearch']=='4c7afb6a97daeb6c0305a07cc0a6b54f3a74f2dc65e387d9b5026333c760b45e'
    env=dict(os.environ,LEAN_PATH=str(lib),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0',PYTHONUTF8='1')
    built=set();replayed=set();active=set()
    def find(module):
        rel=module.replace('.','/')+'.lean'
        return next((p for p in [kit/rel,kit/'lean'/rel,kit/'equivalents'/rel] if p.is_file()),None)
    def build(module):
        if module in built:return
        assert module not in active;active.add(module)
        source=find(module);assert source is not None,module
        rel=source.relative_to(kit).as_posix()
        assert sha(source)==(custom[module] if module in custom else official[rel])
        for dep in re.findall(r'^(?:public\s+)?import\s+([A-Za-z0-9_.]+)',source.read_text(encoding='utf-8'),re.M):
            if dep in custom:assert dep in replayed,(module,dep,'custom dependency not fully replayed')
            if find(dep):build(dep)
            else:assert dep.startswith(('Init','Lean','Std')),dep
        target=lib/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
        run([lean,'-o',target,rel],'build-'+module,env=env)
        built.add(module);active.remove(module)
    for module in ORDER:
        build(module)
        if module in HEADS:heads=[module+'.'+name for name in HEADS[module]]
        else:
            prior=json.loads((published/'formal'/module/'report.json').read_bytes())
            assert prior['source_sha256']==custom[module]
            heads=[h['name'] for h in prior['checker']['headlines']]
        argv=[lean,'--run','Check.lean',module,'--claim','partial']
        for h in heads:argv+=['--headline',h]
        log=run(argv,'replay-'+module,env=env)
        check=json.loads(next(s for s in reversed(log.read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
        assert check['verdict']=='pass' and check['replay']['ok'] and not check['newAxioms']
        assert all(h['ok'] and h['typeMatches'] for h in check['headlines'])
        if module not in HEADS:assert check['replay']['constants']==prior['checker']['replay']['constants']
        report=dict(passed=True,module=module,source_sha256=custom[module],compiled_sha256=sha(lib/(module+'.olean')),
            checker_sha256=CHECKER,kit_pin=PIN,check=check)
        (out/(module+'.json')).write_text(json.dumps(report,indent=2)+'\n')
        results.append(dict(module=module,source_sha256=custom[module],constants=check['replay']['constants'],passed=True))
        replayed.add(module)
        print(json.dumps(results[-1]),flush=True)
    assert sha(kit/'Check.lean')==CHECKER
    report=dict(passed=True,supplied_source_sha256='4c7afb6a97daeb6c0305a07cc0a6b54f3a74f2dc65e387d9b5026333c760b45e',kit_pin=PIN,
        checker_sha256=CHECKER,lean_version=version,modules=results,all_custom_constants=sum(r['constants'] for r in results),
        official_built=sorted(built-set(custom)),seconds=time.monotonic()-started,
        no_reference_cache=True,no_reference_write=True,no_install=True,commands=commands)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='commands'},indent=2))
except BaseException as e:
    (out/'failure.json').write_text(json.dumps(dict(error=repr(e),commands=commands,completed=results,seconds=time.monotonic()-started),indent=2)+'\n')
    raise
