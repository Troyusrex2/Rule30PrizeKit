"""Emit literal-state proof DAGs, with every transition checked by the kernel.

Numerical planning is untrusted: the root proof follows only from checked
child transitions, checked pruning and the generic checker-soundness theorem.
"""
import argparse,hashlib,json,shutil,subprocess,sys,time
from core import HERE,save
from charge_beam_packed import step,controls
from verification_context import add_reference_options,reference

def unpack(d,x):
    A=2*d;B=max(A-1,0)
    return x&((1<<A)-1),(x>>A)&((1<<B)-1),(x>>(A+B))&63,x>>(A+B+6)

def encode(d,R,Rm,g,used):
    A=2*d;B=max(A-1,0)
    return R|(Rm<<A)|(g<<(A+B))|(used<<(A+B+6))

def children(d,x):
    R,Rm,g,used=unpack(d,x);run=g.bit_length()-1
    assert g and g&(g-1)==0 and 0<=run<=5
    R1,Rold=step(R,Rm,2*d,1);base,_=step(R1,Rold,2*d+1,0);pred=(base>>(2*d+1))&1
    out=[]
    for e in [0,1]:
        s=pred^e
        nr=(6 if run==0 else 0) if not s else (6 if run==4 else (1 if run==5 else run+1))
        ng=0 if nr==6 else 1<<nr
        out.append(encode(d+1,base^(((1<<(2*d+2))-1) if s else 0),R1,ng,used+e))
    return out

def pruned(b,d,x):
    _,_,g,u=unpack(d,x)
    return not g or u>b

def main():
    parser=argparse.ArgumentParser();add_reference_options(parser)
    parser.add_argument('--budget',type=int,required=True);parser.add_argument('--horizon',type=int,required=True)
    parser.add_argument('--chunk',type=int,default=128);parser.add_argument('--max-modules',type=int)
    args=parser.parse_args();project,lake,_=reference(args);start=time.monotonic()
    b,K=args.budget,args.horizon;layers=[{32}];edges={};checked=controls()
    for d in range(K):
        nxt=set()
        for x in sorted(layers[-1]):
            cs=children(d,x);edges[d,x]=cs
            nxt.update(y for y in cs if not pruned(b,d+1,y))
        layers.append(nxt)
        if not nxt:break
    assert not layers[-1],'Live states at requested horizon; no proof emitted'
    items=[(d,x) for d in reversed(range(len(layers)-1)) for x in sorted(layers[d])]
    refs={};mods=[];manifest=[];out=HERE/f'golden-budget{b}-dag-evidence';out.mkdir(exist_ok=True)
    for k in range(0,len(items),args.chunk):
        index=k//args.chunk;module=f'Rule30GoldenBudgetDAG{b}Part{index:04d}Research'
        batch=items[k:k+args.chunk];names={key:f'node_{k+i}' for i,key in enumerate(batch)}
        imports={'Rule30GoldenCompactBudgetResearch'};body=[]
        for d,x in batch:
            name=names[d,x];body.append(f'theorem {name} : dfs {b} {K-d} {d} {x} = true := by\n'
                f'  apply dfs_of_children (fuel:={K-d-1})\n')
            for y in edges[d,x]:
                body.append(f'  · change dfs {b} {K-d-1} {d+1} {y} = true\n')
                if pruned(b,d+1,y):body.append('    apply dfs_of_prune\n    decide +kernel\n')
                else:
                    dep,label=refs[d+1,y]
                    if dep!=module:imports.add(dep)
                    body.append(f'    exact {dep}.{label}\n')
            body.append('\n');refs[d,x]=(module,name)
        text=''.join('import '+m+'\n' for m in sorted(imports))
        text+='\nset_option maxRecDepth 200000\nset_option maxHeartbeats 0\n\nnamespace '+module+'\n'
        text+='open Rule30GoldenCompactBudgetResearch\n\n'+''.join(body)+'end '+module+'\n'
        source=HERE/(module+'.lean')
        report=out/module/'report.json';old=source.read_bytes() if source.exists() else None
        if old is not None and old!=text.encode('utf-8') and report.exists():raise RuntimeError('Different replayed DAG source')
        source.write_text(text,encoding='utf-8',newline='\n');digest=hashlib.sha256(source.read_bytes()).hexdigest()
        target=project/source.name
        if target.exists() and target.read_bytes()!=source.read_bytes():
            assert old is not None and target.read_bytes()==old and not report.exists()
            shutil.copyfile(source,target)
        rec={'module':module,'source_sha256':digest,'nodes':len(batch),'index':index};manifest.append(rec);mods.append(module)
        if args.max_modules is not None and index>=args.max_modules:
            save(f'golden-budget{b}-dag-plan.json',{'budget':b,'horizon':K,'unique_live_nodes':len(items),
                'generated_modules':manifest,'planning_not_proof':True})
            print({'stage':'requested_limit','verified_modules':index,'total_unique_nodes':len(items)},flush=True);return
        if report.exists():
            r=json.loads(report.read_text(encoding='utf-8'))
            assert r['source_sha256']==digest and r['check']['verdict']=='pass' and r['check']['replay']['ok']
            assert not r['check']['newAxioms'] and all(h['ok'] for h in r['check']['headlines'])
            print({'module':module,'stage':'retained_exact_replay'},flush=True)
        else:
            print({'module':module,'stage':'fresh_build_replay','nodes':len(batch)},flush=True)
            subprocess.run([sys.executable,str(HERE/'trace_verify.py'),'--module',module,'--headlines',
                names[batch[0]],names[batch[-1]],'--project',str(project),'--lake',str(lake),
                '--output',str(out/module)],cwd=HERE,check=True)
    module=f'Rule30GoldenBudgetDAG{b}Research';root,label=refs[0,32]
    text=f'''import {root}

namespace {module}
open Rule30GoldenCompactBudgetResearch
open Rule30GoldenBudgetResearch (count)

theorem checked : check {b} {K}=true := {root}.{label}

theorem minimum_count (s : Nat → Bool) (hg : Rule30GoldenDFAResearch.Golden s) :
    {b+1} ≤ count s {K} := by
  have hn : ¬ count s {K} ≤ {b} := fun hb => no_golden_of_check checked s hb hg
  omega

theorem no_golden_budget (s : Nat → Bool) (h : ∀ K, count s K ≤ {b}) :
    ¬ Rule30GoldenDFAResearch.Golden s := no_golden_of_check checked s (h {K})

end {module}
'''
    source=HERE/(module+'.lean');source.write_text(text,encoding='utf-8',newline='\n')
    subprocess.run([sys.executable,str(HERE/'trace_verify.py'),'--module',module,'--headlines','checked','minimum_count',
        'no_golden_budget','--project',str(project),'--lake',str(lake),'--output',str(out/module)],cwd=HERE,check=True)
    save(f'golden-budget{b}-dag-plan.json',{'budget':b,'horizon':K,'unique_live_nodes':len(items),'modules':manifest,
        'controls':checked,'all_replayed':True,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)})
    print({'stage':'complete','budget':b,'horizon':K,'modules':len(mods)+1,'unique_live_nodes':len(items)},flush=True)

if __name__=='__main__':main()
