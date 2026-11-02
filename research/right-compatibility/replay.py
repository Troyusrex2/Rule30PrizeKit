import argparse,hashlib,json,os,pathlib,shutil,subprocess,time

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--lean',required=True);ap.add_argument('--out',required=True)
    args=ap.parse_args();root=pathlib.Path(__file__).resolve().parent;out=pathlib.Path(args.out).resolve()
    out.mkdir(parents=True,exist_ok=False);project=out/'project';shutil.copytree(root/'project',project)
    data=json.loads((root/'manifest.json').read_text(encoding='utf-8'))
    for source in data['sources']:
        assert hashlib.sha256((root/source['path']).read_bytes()).hexdigest()==source['sha256']
    assert hashlib.sha256((project/'Check.lean').read_bytes()).hexdigest()==data['checker_sha256']
    env=os.environ.copy();env['LEAN_PATH']=str(project);env['LEAN_NUM_THREADS']='1';begin=time.monotonic()
    receipts=[]
    for module in data['order']:
        rel=pathlib.Path(module.replace('.','/'));source=project/rel.with_suffix('.lean')
        p=subprocess.run([args.lean,'-o',str(project/rel.with_suffix('.olean')),str(source)],cwd=project,
          env=env,capture_output=True,text=True,encoding='utf-8',timeout=60)
        (out/(module+'.build.log')).write_text(p.stdout+p.stderr,encoding='utf-8')
        assert p.returncode==0, module+' build failed'
        if module not in data['headlines']:continue
        cmd=[args.lean,'--run',str(project/'Check.lean'),module,'--claim','partial']
        for h in data['headlines'][module]:cmd+=['--headline',module+'.'+h]
        q=subprocess.run(cmd,cwd=project,env=env,capture_output=True,text=True,encoding='utf-8',timeout=60)
        (out/(module+'.check.log')).write_text(q.stdout+q.stderr,encoding='utf-8')
        assert q.returncode==0,module+' checker failed'
        r=json.loads([line for line in q.stdout.splitlines() if line.startswith('{')][-1])
        assert r['verdict']=='pass' and r['replay']['ok'] and not r['newAxioms'] and not r['verifiedTargets']
        receipts.append({'module':module,'checker':r});print(module+': PASS',flush=True)
    summary={'seconds':time.monotonic()-begin,'compiled':len(data['order']),'audits':receipts}
    (out/'validation.json').write_text(json.dumps(summary,indent=2),encoding='utf-8')
    print(json.dumps({'seconds':summary['seconds'],'compiled':summary['compiled'],'checked':len(receipts)}))

if __name__=='__main__':main()
