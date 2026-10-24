"""Isolate the existing heavy baseline certificate, then resume aggregation."""
import hashlib,importlib.util,json
from core import HERE,BASE,REPO

def main():
    project=BASE/'stripe13-completion-catalog';lake=BASE/'toolchain/lean-4.35.0-windows/bin/lake.exe'
    out=HERE/'tail13-catalog-evidence'
    data=json.loads((HERE/'catalog-tail13-manifest.json').read_text(encoding='utf-8'))
    records=[]
    for entry in data['entries']:
        assert hashlib.sha256((project/entry['source']).read_bytes()).hexdigest()==entry['source_sha256']
        stem=entry['module'].split('.')[-1];log=out/(stem+'.lake-build.log')
        assert 'Build completed successfully' in log.read_text(encoding='utf-8')
        records.append({'module':entry['module'],'source_sha256':entry['source_sha256'],
                        'prior_individual_lake_build_log_verified':True})
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    print({'stage':'isolated_existing_baseline'},flush=True)
    baseline=guard.guarded([str(lake),'build','Ruliology.CellularAutomata.Rule30Certificates.WhitePaddingFamilies'],
        project,out/'WhitePaddingFamilies.isolated.log')
    print({'stage':'baseline_pass','seconds':baseline},flush=True)
    aggregate=guard.guarded([str(lake),'build','Ruliology'],project,out/'Ruliology.resumed-build.log')
    report={'verdict':'pass','module_builds':records,'baseline_isolated_seconds':baseline,
            'aggregate_build_seconds':aggregate,'prior_aggregate_guard_exceeded':True,
            'reason_for_resume':'Existing baseline certificate isolated after aggregate 300-second guard.'}
    (out/'normal-build.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'stage':'normal_build_complete','verdict':'pass'},flush=True)

if __name__=='__main__':main()
