"""Check the exact essay source in a prepared kit; never submit a prize claim."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from verify import HERE, ROOT, run


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lake',default='lake')
    ap.add_argument('--project',type=Path,required=True)
    args=ap.parse_args();project=args.project.resolve()
    checker=subprocess.check_output(['git','show','HEAD:Check.lean'],cwd=project)
    assert (project/'Check.lean').read_bytes().replace(b'\r\n',b'\n')==checker
    config=json.loads((HERE/'notebook-config.json').read_text(encoding='utf-8'))
    source=(HERE/config['SourceFile']).read_bytes()
    name='Rule30RenormalizationReview'
    scratch=project/'.lake/build/review-source';scratch.mkdir(parents=True,exist_ok=True)
    target=scratch/(name+'.lean');target.write_bytes(source)
    output=project/'.lake/build/lib/lean'/(name+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
    evidence=HERE/'evidence';evidence.mkdir(exist_ok=True)
    build=run([args.lake,'env','lean','--root',str(scratch),'-o',str(output),str(target)],
              project,evidence/'standalone.build.log')
    argv=[args.lake,'env','lean','--run','Check.lean',name,'--claim','partial']
    for h in config['Headlines']:argv+=['--headline',h]
    log=evidence/'standalone.check.log';seconds=run(argv,project,log)
    data=json.loads([l for l in log.read_text(encoding='utf-8').splitlines() if l.startswith('{')][-1])
    assert data['verdict']=='pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    report={'verdict':'pass','checker_modified':False,'prize_API_submitted':False,
            'full_problem_claim':False,'CQ01Empty_proved':False,
            'source_sha256':hashlib.sha256(source).hexdigest(),
            'kit_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip(),
            'build_seconds':build,'check_seconds':seconds,'native_C_emitted':False,'check':data}
    (HERE/'standalone-verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'verdict':'pass','constants':data['replay']['constants'],
                      'headlines':len(data['headlines']),'source_sha256':report['source_sha256']}))


if __name__=='__main__':main()
