"""Choose bounded proof subtrees; numerical planning is never a proof premise."""
import argparse,json,time
from core import HERE,save
from charge_beam_packed import step,controls
from coupled_even_code_probe import decode,forbidden

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--budget',type=int,default=8)
    parser.add_argument('--horizon',type=int,default=102);parser.add_argument('--max-nodes',type=int,default=4000)
    args=parser.parse_args();start=time.monotonic();checked=controls();sizes={};pruned=set()
    def walk(u,n,R,Rm,run):
        key=(n,u)
        if u.bit_count()>args.budget or run==6:pruned.add(key);sizes[key]=0;return 0
        if n==args.horizon:raise RuntimeError('Live leaf at requested horizon; no extinction plan')
        R1,Rold=step(R,Rm,2*n,1);base,_=step(R1,Rold,2*n+1,0);pred=base>>(2*n+1)&1
        total=1;mask=(1<<(2*n+2))-1
        for bit in [0,1]:
            s=pred^bit
            nr=(6 if run==0 else 0) if not s else (6 if run in [4,6] else (1 if run==5 else run+1))
            total+=walk(u|(bit<<n),n+1,base^(mask if s else 0),R1,nr)
        sizes[key]=total;return total
    total=walk(0,0,0,0,5);skeleton=[];leaves=[]
    def select(u,n):
        key=(n,u)
        if key in pruned:
            skeleton.append({'kind':'prune','n':n,'u':u});return
        if sizes[key]<=args.max_nodes:
            leaf={'kind':'leaf','n':n,'u':u,'index':len(leaves),'estimated_nodes':sizes[key]}
            leaves.append(leaf);skeleton.append(leaf);return
        select(u,n+1);select(u|(1<<n),n+1)
        skeleton.append({'kind':'branch','n':n,'u':u})
    select(0,0)
    # Independent physical prefix controls at every chosen proof leaf.
    for leaf in leaves:
        assert forbidden(decode(leaf['u'],leaf['n'])) is None
    out={'budget':args.budget,'horizon':args.horizon,'max_nodes':args.max_nodes,
         'total_live_nodes':total,'skeleton':skeleton,'leaves':leaves,'controls':checked,
         'physical_leaf_prefix_controls':len(leaves),'Lean_verified':False,
         'planning_not_proof_premise':True,'seconds':round(time.monotonic()-start,3)}
    save(f'golden-budget{args.budget}-partition-plan.json',out)
    print({k:out[k] for k in ['budget','horizon','total_live_nodes','seconds']},flush=True)
    print({'proof_leaves':len(leaves),'skeleton_nodes':len(skeleton),'largest_leaf':max(a['estimated_nodes'] for a in leaves)},flush=True)

if __name__=='__main__':main()
