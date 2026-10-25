"""Partition the complete budget-eight proof into bounded, resumable kernel jobs."""
import hashlib,json,sys,zipfile
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from core import HERE
import plan_golden_budget_partition as planner
from build_golden_budget_dag import children

ROOT=Path(__file__).resolve().parent

def main():
    dest=ROOT/'_cache/budget8-c600';dest.mkdir(parents=True,exist_ok=True)
    def save_plan(_,value):(dest/'plan.json').write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8')
    planner.save=save_plan;sys.argv=['planner','--budget','8','--horizon','102','--max-nodes','600'];planner.main()
    plan=json.loads((dest/'plan.json').read_text());refs={};modules=[];files={}
    def put(name,raw):
        data=raw.encode('utf-8') if isinstance(raw,str) else raw
        target=dest/name;target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists():assert target.read_bytes()==data,name
        else:target.write_bytes(data)
        files[name]=hashlib.sha256(data).hexdigest()
    for leaf in plan['leaves']:
        i,n,u=leaf['index'],leaf['n'],leaf['u'];m=f'Rule30GoldenBudget8C600Part{i:04d}Research';x=32
        for d in range(n):x=children(d,x)[(u>>d)&1]
        src=f'''import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace {m}
open Rule30GoldenCompactBudgetResearch

def q : Nat := {x}

theorem path_eq : path {u} {n}=q := by rfl

theorem literal_cert : dfs 8 {102-n} {n} q=true := by decide +kernel

theorem cert : dfs 8 {102-n} {n} (path {u} {n})=true := by
  rw [path_eq]
  exact literal_cert

end {m}
'''
        name='sources/'+m+'.lean';put(name,src);modules.append({'module':m,'source':name,'headlines':['path_eq','literal_cert','cert'],
            'prefix_length':n,'estimated_nodes':leaf['estimated_nodes']});refs[n,u]=m+'.cert'
    m='Rule30GoldenBudget8C600Research';src='import Rule30GoldenCompactPathResearch\n'
    src+=''.join('import '+r['module']+'\n' for r in modules)
    src+='\nset_option maxRecDepth 200000\nset_option maxHeartbeats 0\n\nnamespace '+m+'\n'
    src+='open Rule30GoldenCompactBudgetResearch\nopen Rule30GoldenCompactPathResearch\nopen Rule30GoldenBudgetResearch (count)\n\n'
    for node in plan['skeleton']:
        n,u,kind=node['n'],node['u'],node['kind']
        if kind=='leaf':continue
        label=f'node_{n}_{u}';src+=f'theorem {label} : dfs 8 {102-n} {n} (path {u} {n})=true := by\n'
        if kind=='prune':src+='  apply dfs_of_prune\n  decide +kernel\n\n'
        else:
            src+=f'  apply dfs_of_children (fuel:={101-n})\n'
            src+=f'  · have hc := {refs[n+1,u]}\n'
            src+=f'    rw [zero_extension {u} {n} (by decide +kernel)] at hc\n    exact hc\n'
            src+=f'  · have hc := {refs[n+1,u|(1<<n)]}\n'
            src+=f'    change dfs 8 {101-n} {n+1} (path ({u} ||| 2^{n}) ({n}+1))=true at hc\n'
            src+=f'    rw [one_extension {u} {n}] at hc\n    exact hc\n\n'
        refs[n,u]=label
    src+=f'theorem checked : check 8 102=true := {refs[0,0]}\n\n'
    src+='''theorem minimum_nine (s : Nat → Bool) (hg : Rule30GoldenDFAResearch.Golden s) :
    9 ≤ count s 102 := by
  have hn : ¬ count s 102 ≤ 8 := fun hb => no_golden_of_check checked s hb hg
  omega

theorem no_golden_eight (s : Nat → Bool) (h : ∀ K, count s K ≤ 8) :
    ¬ Rule30GoldenDFAResearch.Golden s := no_golden_of_check checked s (h 102)

'''+f'end {m}\n'
    put('sources/'+m+'.lean',src)
    put('sources/Rule30GoldenCompactPathResearch.lean',(HERE/'Rule30GoldenCompactPathResearch.lean').read_bytes())
    put('budget8_worker.py',(ROOT/'budget8_worker.py').read_bytes())
    # Include the planner's immutable record as untrusted data with its own hash.
    files['plan.json']=hashlib.sha256((dest/'plan.json').read_bytes()).hexdigest()
    manifest={'modules':modules,'root':{'module':m,'source':'sources/'+m+'.lean','headlines':['checked','minimum_nine','no_golden_eight']},
       'helper':{'module':'Rule30GoldenCompactPathResearch','source':'sources/Rule30GoldenCompactPathResearch.lean',
                 'headlines':['path_congr','path_or_pow_prefix','zero_extension','one_extension']},
       'files':files,'limits':{'seconds':300,'rss_gib':8,'minimum_free_gib':16},'workers':3,
       'budget':8,'horizon':102,'full_problem_solved':False,'planning_is_not_proof':True}
    raw=json.dumps(manifest,indent=2)+'\n';(dest/'batch-manifest.json').write_text(raw,encoding='utf-8')
    archive=ROOT/'_cache/budget8-c600.zip'
    with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=1) as z:
        for name in sorted(files):z.write(dest/name,name)
        z.writestr('batch-manifest.json',raw)
    with archive.open('rb') as f:digest=hashlib.file_digest(f,'sha256').hexdigest()
    (ROOT/'_cache/budget8-transfer.json').write_text(json.dumps({'sha256':digest,'archive_bytes':archive.stat().st_size,
        'leaf_modules':len(modules),'largest_leaf':max(r['estimated_nodes'] for r in modules)},indent=2)+'\n',encoding='utf-8')
    print({'archive_sha256':digest,'leaf_modules':len(modules),'largest_leaf':max(r['estimated_nodes'] for r in modules)},flush=True)

if __name__=='__main__':main()
