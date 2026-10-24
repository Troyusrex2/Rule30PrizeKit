"""Propose bit-parallel endpoints; only the generated Lean checks can certify them."""
import hashlib,json
from pathlib import Path
from core import HERE,phi

OUT=HERE/'front-jump';K=34;M=12;N=1<<M

def combine(proofs):
    if len(proofs)==1:return proofs[0]
    n=len(proofs)//2
    return '(run_chain '+combine(proofs[:n])+' '+combine(proofs[n:])+')'

def state(lo,phase,planes):
    return '⟨'+str(lo)+', '+str(phase)+', ['+', '.join(hex(p) for p in planes)+']⟩'

def main():
    OUT.mkdir(exist_ok=True);ALL=(1<<N)-1;lowmask=(1<<K)-1
    planes=[sum(((u>>i)&1)<<u for u in range(N)) for i in range(M)]
    lo=13;points=[0,*range(8192,57345,8192),61005,65536];states=[]
    for t in range(65537):
        if t in points:states.append({'time':t,'lo':lo,'phase':t%2,'planes':planes.copy()})
        if t==65536:break
        l=ALL if lo>>(K-1)&1 else 0;r=ALL if lo>>(K-2)&1 else 0;new=[]
        for a in planes:new.append(a^(l|r));r,l=l,a
        lo=(phi(lo)^1)&lowmask;planes=new
    assert len(states)==10 and states[-1]['lo']==13
    lines=['import Rule30FrontLanesResearch','','namespace Rule30FrontJumpResearch',
           'open Rule30FrontLanesResearch','']
    for j,s in enumerate(states):
        lines += [f'def state{j:03d} : LaneState := '+state(s['lo'],s['phase'],s['planes']),'']
    lines += ['theorem initial_eq : initial 12 13 0 = state000 := by decide +kernel','',
              'end Rule30FrontJumpResearch','']
    dataModule='Rule30FrontJumpStatesResearch'
    (OUT/(dataModule+'.lean')).write_text('\n'.join(lines),encoding='utf-8',newline='\n')
    entries=[{'module':dataModule,'heads':['initial_eq']}]
    for j in range(9):
        module=f'Rule30FrontJumpChunk{j:02d}Research';length=points[j+1]-points[j]
        lines=['import '+dataModule,'','set_option maxRecDepth 200000','set_option maxHeartbeats 0','',
               'namespace Rule30FrontJumpResearch','open Rule30FrontLanesResearch','',
               f'theorem run_{j:02d} : run 34 (allMask 12) {length} state{j:03d} = state{j+1:03d} := by',
               '  decide +kernel','','end Rule30FrontJumpResearch','']
        (OUT/(module+'.lean')).write_text('\n'.join(lines),encoding='utf-8',newline='\n')
        entries.append({'module':module,'heads':[f'run_{j:02d}']})
    root='Rule30FrontJumpExecutionResearch'
    lines=['import '+x['module'] for x in entries[1:]]+['','namespace Rule30FrontJumpResearch',
           'open Rule30FrontLanesResearch','',
           'theorem run_prefix : run 34 (allMask 12) 61005 (initial 12 13 0) = state008 := by',
           '  rw [initial_eq]', '  exact '+combine([f'run_{j:02d}' for j in range(8)]),'',
           'theorem run_full : run 34 (allMask 12) 65536 (initial 12 13 0) = state009 := by',
           '  rw [initial_eq]', '  exact '+combine([f'run_{j:02d}' for j in range(9)]),'',
           'end Rule30FrontJumpResearch','']
    (OUT/(root+'.lean')).write_text('\n'.join(lines),encoding='utf-8',newline='\n')
    entries.append({'module':root,'heads':['run_prefix','run_full']})
    data={'entries':entries,'times':points,'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
          for p in OUT.glob('*.lean')},'Lean_verified':False,'full_problem_solved':False}
    (OUT/'generation.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'modules':len(entries),'lanes':N,'parallel_steps':65536},flush=True)

if __name__=='__main__':main()
