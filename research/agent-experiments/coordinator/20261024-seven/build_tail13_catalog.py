"""Validate normal Lake build targets with at most two independent jobs."""
import concurrent.futures,hashlib,importlib.util,json
from core import HERE,BASE,REPO

def main():
    project=BASE/'stripe13-completion-catalog';lake=BASE/'toolchain/lean-4.35.0-windows/bin/lake.exe'
    data=json.loads((HERE/'catalog-tail13-manifest.json').read_text(encoding='utf-8'))
    checked=json.loads((HERE/'tail13-catalog-evidence/report.json').read_text(encoding='utf-8'))
    assert checked['verdict']=='pass'
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    out=HERE/'tail13-catalog-evidence';records=[]
    def build(entry):
        name=entry['module'];stem=name.split('.')[-1]
        assert hashlib.sha256((project/entry['source']).read_bytes()).hexdigest()==entry['source_sha256']
        print({'target':stem,'stage':'lake_build'},flush=True)
        seconds=guard.guarded([str(lake),'build',name],project,out/(stem+'.lake-build.log'))
        print({'target':stem,'stage':'lake_build_pass','seconds':seconds},flush=True)
        return {'module':name,'seconds':seconds}
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        records=list(pool.map(build,data['entries'][:-1]))
    records.append(build(data['entries'][-1]))
    print({'stage':'catalog_aggregate_build'},flush=True)
    seconds=guard.guarded([str(lake),'build','Ruliology'],project,out/'Ruliology.lake-build.log')
    result={'verdict':'pass','module_builds':records,'aggregate_build_seconds':seconds}
    (out/'normal-build.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'stage':'normal_build_complete','verdict':'pass'},flush=True)

if __name__=='__main__':main()
