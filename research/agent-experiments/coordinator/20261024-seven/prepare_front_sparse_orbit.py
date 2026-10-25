"""Certify only the 32 visited upper states, using the general parallel semantics.

The proposed constants are all checked by the kernel. The complete orbit
proof uses the general finite-return-map theorem with a 32-state index map.
"""
import hashlib,json,shutil
from core import HERE,BASE,phi
from prepare_front_tools_review import PROJECT,CA,CORE,DATA,FINAL,header,body,MAPPING
from generate_front_jump import combine,state

def main():
    manifest=json.loads((HERE/'front-tools-reviewed-manifest.json').read_text(encoding='utf-8'))
    oldout=HERE/'front-tools-reviewed-evidence';archive=HERE/'front-tools-4096-lane-baseline'
    if not archive.exists():
        archive.mkdir()
        for entry in manifest['entries']:
            raw=(PROJECT/entry['source']).read_bytes();assert hashlib.sha256(raw).hexdigest()==entry['source_sha256']
            target=archive/PathName(entry['source']);target.write_bytes(raw)
        for p in oldout.iterdir():
            if p.is_file():shutil.copyfile(p,archive/p.name)
        shutil.copyfile(HERE/'front-tools-reviewed-manifest.json',archive/'manifest.json')
    raw=json.loads((HERE/'jump-table-12-data.json').read_text(encoding='utf-8'))
    J=raw['return'];seeds=[];u=0
    while u not in seeds:seeds.append(u);u=J[u]
    assert u==0 and len(seeds)==32 and all(0<=v<4096 for v in seeds)
    ALL=(1<<32)-1;lo=13;planes=[sum(((u>>i)&1)<<j for j,u in enumerate(seeds)) for i in range(12)]
    points=[0,*range(8192,57345,8192),61005,65536];states=[]
    for t in range(65537):
        if t in points:states.append({'time':t,'lo':lo,'phase':t%2,'planes':planes.copy()})
        if t==65536:break
        l=ALL if lo>>33&1 else 0;r=ALL if lo>>32&1 else 0;out=[]
        for a in planes:out.append(a^(l|r));r,l=l,a
        lo=(phi(lo)^1)&((1<<34)-1);planes=out
    assert len(states)==10
    def upper(st,j):return sum((p>>j&1)<<i for i,p in enumerate(st['planes']))
    assert [upper(states[-1],j) for j in range(32)]==[seeds[(j+1)%32] for j in range(32)]
    assert all((states[-2]['lo']|(upper(states[-2],j)<<34))==raw['prefix'][u] for j,u in enumerate(seeds))
    data=header([CORE],
        'Certificate data for the tail-13 completion. A punctured width-34\n'+
        'cycle and 32 parallel upper states certify a width-46 return cycle.')
    data+='set_option maxRecDepth 200000\nset_option maxHeartbeats 0\n\nnamespace '+DATA+'\n'
    data+='open '+CORE+'\nopen '+CA+'Rule30ZeroBoundaryStripeFront\n\n'
    data+='def lanes : Nat := 2^32-1\n\ndef seeds : List Nat := ['+','.join(map(str,seeds))+']\n\n'
    data+='def embedding (j : Nat) : Nat := 13 ||| (seeds.getD j 0 <<< 34)\n\n'
    data+='def nextIndex (j : Nat) : Nat := (j+1)%32\n\n'
    for i,s in enumerate(states):data+=f'def state{i:03d} : LaneState := '+state(s['lo'],s['phase'],s['planes'])+'\n\n'
    for i in range(9):
        data+=f'theorem run_{i:02d} : run 34 lanes {points[i+1]-points[i]} state{i:03d} = state{i+1:03d} := by decide +kernel\n\n'
    for name,t,count,endpoint in [('prefix',61005,8,8),('full',65536,9,9)]:
        data+=f'theorem run_{name} : run 34 lanes {t} state000 = state{endpoint:03d} :=\n  '+combine([f'run_{i:02d}' for i in range(count)])+'\n\n'
    data+='''def prefixWord (j : Nat) : Nat := word 34 (project j state008)

theorem initial_words : (List.range 32).all (fun j =>
    word 34 (project j state000) == embedding j) = true := by decide +kernel

theorem endpoint_words : (List.range 32).all (fun j =>
    word 34 (project j state009) == embedding (nextIndex j)) = true := by decide +kernel

theorem initial_word (j : Nat) (hj : j < 32) : word 34 (project j state000) = embedding j :=
  Nat.beq_eq.mp (List.all_eq_true.mp initial_words j (List.mem_range.mpr hj))

theorem endpoint_word (j : Nat) (hj : j < 32) : word 34 (project j state009) = embedding (nextIndex j) :=
  Nat.beq_eq.mp (List.all_eq_true.mp endpoint_words j (List.mem_range.mpr hj))

theorem rare_table : (List.range 32).all (fun j =>
    sig 46 (65536*j+61005) (prefixWord j)) = true := by decide +kernel

theorem rare_table_sound (j : Nat) (hj : j < 32) :
    sig 46 (65536*j+61005) (prefixWord j) = true :=
  List.all_eq_true.mp rare_table j (List.mem_range.mpr hj)

theorem return_cycle : iter nextIndex 32 0 = 0 := by decide +kernel

theorem index_table : (List.range 32).all (fun j => iter nextIndex j 0 == j) = true := by decide +kernel

theorem iter_index (j : Nat) (hj : j < 32) : iter nextIndex j 0 = j :=
  Nat.beq_eq.mp (List.all_eq_true.mp index_table j (List.mem_range.mpr hj))

theorem lanes_bit (j : Nat) (hj : j < 32) : lanes.testBit j = true := by
  unfold lanes
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj

'''
    original_raw=(HERE/'external/QuintGeminiFiveTail-f177ae.lean').read_bytes()
    assert hashlib.sha256(original_raw).hexdigest()=='b84849e8f368b030550f586f1c2808e3da74e28e9d93b6b99d808de4f9942689'
    original=original_raw.decode('utf-8')
    data+=original[original.index('theorem seg13_0'):original.index('/-- **Control check at `r = 61005`')]
    data+=original[original.index('theorem cyc13_period'):original.index('/-- **Punctured front-window soundness')]
    data+='\nend '+DATA+'\n'
    root=PROJECT/'lean/Ruliology/CellularAutomata';(root/'Rule30Certificates/StripeTail13Completion.lean').write_text(data,encoding='utf-8',newline='\n')
    final=header([CA+'Rule30Certificates.StripeTail13Completion',CA+'Rule30ZeroBoundaryStripeFour'],
        'Complete four-bit stripe-prefix tails, including every odd prefix\n'+
        'with tail 13, using a sparse 32-state upper return orbit.')
    final+='namespace '+FINAL+'\nopen Ruliology.CellularAutomata\n'
    final+='open Rule30ZeroBoundaryStripeFront Rule30ZeroBoundary\nopen '+CORE+' '+DATA+'\n\n'
    final+='''theorem full_jump (j : Nat) (hj : j < 32) :
    orb 46 65536 (embedding j,0) = (embedding (nextIndex j),0) := by
  have h := run_correct (ALL:=lanes) (p:=j) (K:=34) (s:=state000)
    (lanes_bit j hj) (by decide) (by decide) (by decide) 65536
  rw [run_full, initial_word j hj, endpoint_word j hj] at h
  exact h

theorem prefix_jump (j : Nat) (hj : j < 32) :
    orb 46 61005 (embedding j,0) = (prefixWord j,1) := by
  have h := run_correct (ALL:=lanes) (p:=j) (K:=34) (s:=state000)
    (lanes_bit j hj) (by decide) (by decide) (by decide) 61005
  rw [run_prefix, initial_word j hj] at h
  exact h

theorem compressed_cycle : Cycle 46 45 13 0 2097152 := by
  change Cycle 46 45 (embedding 0) 0 (65536*32)
  apply return_map_cycle_lift (Klo:=34) (Khi:=46) (Slo:=33) (Shi:=45)
    (B:=13) (p:=0) (L:=65536) (N:=32) (u:=0) (q:=32)
    (J:=nextIndex) (embed:=embedding) (E:=fun r => r=61005)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ => rfl)
    (by decide) (by decide) cyc13_period
  · intro r hr hp hne
    exact cyc13_sig r hr hp hne
  · intro v _
    exact Nat.mod_lt (v+1) (by decide)
  · decide
  · exact full_jump
  · decide
  · exact return_cycle
  · intro j hj e _ _ he
    subst e
    rw [iter_index j hj,prefix_jump j hj]
    exact rare_table_sound j hj

'''
    old=(HERE/'front-jump/Rule30FrontJumpCycleResearch.lean').read_text(encoding='utf-8')
    final+=old[old.index('theorem compressed_row4_13'):old.rfind('\nend ')]+'\n\n'
    final+='theorem cycle13_complete : Cycle 46 45 13 0 2097152 := compressed_cycle\n\n'
    old=(BASE/'stripe13-completion-catalog/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryStripeFourComplete.lean').read_text(encoding='utf-8')
    final+=old[old.index('theorem row4_13_all_odd'):old.rfind('\nend ')]+'\n\nend '+FINAL+'\n'
    (root/'Rule30ZeroBoundaryStripeFourComplete.lean').write_text(final,encoding='utf-8',newline='\n')
    for entry in manifest['entries']:
        entry['source_sha256']=hashlib.sha256((PROJECT/entry['source']).read_bytes()).hexdigest()
    manifest['upper_lanes']=32;manifest['upper_orbit']=seeds
    (HERE/'front-tools-reviewed-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'upper_states':32,'parallel_steps':65536,'certificate_source_bytes':len(data.encode()),
           'family_source_bytes':len(final.encode()),'all_computations_still_need_kernel_replay':True},flush=True)

def PathName(source):return source.rsplit('/',1)[-1]

if __name__=='__main__':main()
