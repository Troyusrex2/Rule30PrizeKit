"""Generate exact front-cycle certificates, not trusted computational premises."""
from pathlib import Path
import hashlib,json
from core import HERE

OUT=HERE/'tail13-completion'
N=2097152;K=46;S=45;SEG=8192;PER_FILE=8

def combine(exprs):
    if len(exprs)==1:return exprs[0]
    mid=len(exprs)//2
    return '(path_append '+combine(exprs[:mid])+' '+combine(exprs[mid:])+')'

def main():
    OUT.mkdir(exist_ok=True);states=[13];w=13;mask=(1<<K)-1
    for r in range(N):
        fp=r%2
        # Exact published fstep, independent of the simplified JIT scanner.
        w=(w^((w<<1)|(1-fp)|(w<<2)|((1-fp)<<1)|fp))&mask
        if (r+1)%SEG==0:states.append(w)
    assert states[-1]==13 and len(states)==257
    modules=[]
    for chunk in range(32):
        module=f'Rule30Tail13Chunk{chunk:02d}';modules.append(module)
        lines=['module','',
            'public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront','',
            '/-! One exact segment of the complete (13,0) front-window certificate.',
            'Every Boolean computation is replayed by the Lean kernel. -/','',
            'set_option maxRecDepth 200000','set_option maxHeartbeats 0','',
            '@[expose] public section','',
            'namespace Ruliology.CellularAutomata.Rule30Tail13Completion',
            'open Rule30ZeroBoundaryStripeFront','']
        proofs=[]
        for j in range(PER_FILE):
            i=chunk*PER_FILE+j;r=i*SEG;old=states[i];new=states[i+1]
            lines += [f'theorem seg_{i:03d} : seg {K} {S} 1 {new} 0 {SEG} {r} {old} 0 = true := by',
                      '  decide +kernel','']
            proofs.append(f'(seg_sound {K} {S} 1 {new} 0 {SEG} {r} {old} 0 seg_{i:03d})')
        begin=chunk*PER_FILE;end=begin+PER_FILE
        lines += [f'theorem path_chunk_{chunk:02d} : PathOK {K} {S} 1 {begin*SEG} ({states[begin]}, 0) ({states[end]}, 0) {SEG*PER_FILE} :=',
                  '  '+combine(proofs),'',
                  'end Ruliology.CellularAutomata.Rule30Tail13Completion','']
        (OUT/(module+'.lean')).write_text('\n'.join(lines),encoding='utf-8',newline='\n')
    lines=['module','']+['public import '+m for m in modules]+['',
        'public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFour','',
        '/-! Completes the omitted odd-prefix / tail-13 family in the official',
        'four-tail stripe theorem. The certificate has width 46 and period 2^21.',
        'This is not Q01 or a solution of a prize problem. -/','',
        '@[expose] public section','',
        'namespace Ruliology.CellularAutomata.Rule30Tail13Completion',
        'open Rule30ZeroBoundaryStripeFront Rule30ZeroBoundary','',
        f'theorem complete_path : PathOK {K} {S} 1 0 (13, 0) (13, 0) {N} :=',
        '  '+combine([f'path_chunk_{i:02d}' for i in range(32)]),'',
        f'theorem cycle13_complete : Cycle {K} {S} 13 0 {N} :=',
        '  ⟨by decide, by decide, complete_path⟩','',
        'theorem row4_13_all_odd (m : Nat) (hq : m % 2 = 1) :',
        '    (∀ k, 1 ≤ k → k < m + 1 → row4 m 13 k = stripe k) ∧',
        '      row4 m 13 (m + 1) ≠ stripe (m + 1) ∧',
        '      ∃ t, t ≤ m + 45 ∧ t % 2 = 0 ∧ zrow (row4 m 13) t 1 = false := by',
        '  have hag : ∀ k, 1 ≤ k → k < m + 1 → row4 m 13 k = stripe k := by',
        '    intro k _ hk; unfold row4; rw [ite_eq_left (by omega)]',
        '  have hdev : row4 m 13 (m + 1) ≠ stripe (m + 1) := by',
        '    unfold row4',
        '    rw [ite_eq_right (by omega), show m + 1 - m - 1 = 0 by omega,',
        '      stripe_add_mod m 1 1 hq]',
        '    decide',
        '  have hwin : pk (fun i => row4 m 13 (m + 1 + i)) 46 = 13 := by',
        '    have hw : pk (fun i => row4 m 13 (m + 1 + i)) 46 = pk (tail4 13) 46 :=',
        '      pk_congr _ _ _ fun i _ => by',
        '        unfold row4',
        '        rw [ite_eq_right (by omega), show m + 1 + i - m - 1 = i by omega]',
        '    rw [hw]; decide +kernel',
        '  have hcyc : Cycle 46 45 (pk (fun i => row4 m 13 (m + 1 + i)) 46)',
        '      ((m + 1) % 2) 2097152 := by',
        '    rw [hwin, show (m + 1) % 2 = 0 by omega]',
        '    exact cycle13_complete',
        '  obtain ⟨s, hs, he, hz⟩ := front_sound (row4 m 13) (m + 1) 46 45 2097152',
        '    (by omega) hag (by omega) hcyc',
        '  exact ⟨hag, hdev, m + s, by omega, by simpa using he, by simpa using hz⟩','',
        'theorem stripe_four_tail_complete (m : Nat) (v : Fin 16) :',
        '    ∃ d, 1 ≤ d ∧ d ≤ m + 6 ∧',
        '      (∀ k, 1 ≤ k → k < d → row4 m v.val k = stripe k) ∧',
        '      row4 m v.val d ≠ stripe d ∧',
        '      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row4 m v.val) t 1 = false := by',
        '  by_cases h : v.val ≠ 13 ∨ m % 2 = 0',
        '  · obtain ⟨d, hd, hdm, hag, hdev, t, ht, he, hz⟩ := stripe_four_tail m v h',
        '    exact ⟨d, hd, hdm, hag, hdev, t, by omega, he, hz⟩',
        '  · have hv : v.val = 13 := by omega',
        '    have hq : m % 2 = 1 := by omega',
        '    rw [hv]',
        '    obtain ⟨hag, hdev, t, ht, he, hz⟩ := row4_13_all_odd m hq',
        '    exact ⟨m + 1, by omega, by omega, hag, hdev, t, by omega, he, hz⟩','',
        'end Ruliology.CellularAutomata.Rule30Tail13Completion','']
    (OUT/'Rule30Tail13Complete.lean').write_text('\n'.join(lines),encoding='utf-8',newline='\n')
    data={'width':K,'postarrival_bound':S,'period':N,'segment_length':SEG,'chunks':32,
          'segments_per_chunk':PER_FILE,'segment_endpoints':states,'modules':modules+['Rule30Tail13Complete'],
          'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.glob('*.lean'))},
          'Lean_verified':False,'full_problem_solved':False}
    (OUT/'generation.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'generated_modules':33,'cycle_steps':N,'all_endpoints_return':states[-1]==13},flush=True)

if __name__=='__main__':main()
