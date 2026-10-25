"""Measure the original monolithic data alone, with identical pinned imports."""
import hashlib,json,shutil,subprocess
from core import HERE,BASE
from verify_reviewed_front_catalog import measured,LAKE,PIN

project=BASE/'current-reference-3eca-20261024';manifest=json.loads((HERE/'tail13-baseline-manifest.json').read_text(encoding='utf-8'))
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==PIN
source=HERE/'Rule30Tail13MergedBaseline.lean';raw=source.read_bytes()
assert hashlib.sha256(raw).hexdigest()==manifest['source_sha256']
target=project/source.name
if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different owned baseline source')
shutil.copyfile(source,target);out=HERE/'tail13-baseline-evidence';out.mkdir(exist_ok=True)
result=measured([str(LAKE),'env','lean','-o',str(project/'.lake/build/lib/lean/Rule30Tail13MergedBaseline.olean'),str(target)],
                project,out/'normal-compile.log')
info={**manifest,'kit_base':PIN,'normal_compiler':True,'imports_already_compiled':True,'build':result,
      'benchmark_only_no_new_mathematical_claim':True}
(out/'report.json').write_text(json.dumps(info,indent=2)+'\n',encoding='utf-8',newline='\n')
print({'baseline_compile_seconds':result['seconds'],'peak_gb':round(result['peak_tree_rss_bytes']/1e9,3)},flush=True)
