"""Create a fresh V2 control directory with efficient joins, keeping V1 immutable."""
import hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent;old=root/'_cache/budget8-c600';new=root/'_cache/budget8-c600-v2'
manifest=json.loads((old/'batch-manifest.json').read_text(encoding='utf-8'))
def put(name,data):
 p=new/name;p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==data,name
 else:p.write_bytes(data)
 return hashlib.sha256(data).hexdigest()
for name,digest in manifest['files'].items():
 data=(old/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest
 put(name,data)
s=(old/manifest['root']['source']).read_text(encoding='utf-8').replace('Rule30GoldenBudget8C600Research','Rule30GoldenBudget8C600V2Research')
pattern=r'    change dfs 8 (\d+) (\d+) \(path \((\d+) \|\|\| 2\^(\d+)\) \((\d+)\+1\)\)=true at hc\n    rw \[one_extension (\d+) (\d+)\] at hc'
def fix(m):
 fuel,dep,u,n,nn,uu,nnn=map(int,m.groups());assert dep==n+1 and n==nn==nnn and u==uu
 return f'    have hn : ({u} ||| 2^{n})={u|(1<<n)} := by decide +kernel\n    have hp := one_extension {u} {n}\n    rw [hn] at hp\n    rw [hp] at hc'
s,count=re.subn(pattern,fix,s);assert count==640
name='sources/Rule30GoldenBudget8C600V2Research.lean';digest=put(name,s.encode('utf-8'))
assert digest=='d5c324aa260a83c3a2508d5652bc7a628eaa83612e3037f2d979c84f5a770087'
manifest['files'][name]=digest;manifest['root']={'module':'Rule30GoldenBudget8C600V2Research','source':name,'headlines':['checked','minimum_nine','no_golden_eight']}
manifest['join_version']=2;put('batch-manifest.json',(json.dumps(manifest,indent=2)+'\n').encode('utf-8'))
print({'corrected_joins':count,'root_sha256':digest,'directory':new.name},flush=True)
