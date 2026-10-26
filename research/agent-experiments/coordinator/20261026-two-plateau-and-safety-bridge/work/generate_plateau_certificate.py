from pathlib import Path
import json
root=Path(__file__).resolve().parent

def good(q):
    a,b=q%64,q//64
    return bool((a&48) and (b&48) and ((a^b)&8) and not ((a^b)&4))

def row_step(a,u):return ((a^((a<<1)|(a<<2)))&60)|(u&3)
def advance(q,u):return row_step(q%64,u%4)+64*row_step(q//64,u//4)

def literal_row(a,u):
    old=[(a>>i)&1 for i in range(6)]
    new=[u&1,(u>>1)&1]+[old[i]^(old[i-1]|old[i-2]) for i in range(2,6)]
    return sum(b<<i for i,b in enumerate(new))

for a in range(64):
    for u in range(4):assert row_step(a,u)==literal_row(a,u)
levels=[{q for q in range(4096) if good(q)}]
for _ in range(3):
    old=levels[-1]
    levels.append({q for q in old if any(advance(q,u) in old for u in range(16))})
live=levels[-1]
assert [len(x) for x in levels]==[576,152,92,70]
assert {q for q in live if any(advance(q,u) in live for u in range(16))}==live
succ={q:sorted({advance(q,u) for u in range(16) if advance(q,u) in live}) for q in live}
def proj(q):return (q%64)//4+16*((q//64)//4)
def swap(p):return p//16+16*(p%16)
projections=sorted({proj(q) for q in live})
reach={}
for p in projections:
    found={q for q in live if proj(q)==p};todo=list(found)
    while todo:
        q=todo.pop()
        for r in succ[q]:
            for s in succ[r]:
                if s not in found:found.add(s);todo.append(s)
    assert all(proj(q)!=swap(p) for q in found)
    reach[p]=found
def mask(xs):return sum(1<<q for q in xs)
def ls(xs):return '['+','.join(map(str,sorted(xs)))+']'
prelude='''module
public import Ruliology.CellularAutomata.Rule30Prize

/-! A finite paired-strip certificate. All tables are kernel checked.
The generic path proof and Actual semantic bridge live in the next module. -/
@[expose] public section
namespace Rule30PlateauPairCertificate
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

def bits : List Nat → Nat
  | [] => 0
  | x::xs => (2^x) ||| bits xs

theorem bits_mem (xs : List Nat) (q : Nat) : (bits xs).testBit q=true ↔ q∈xs := by
  induction xs with
  | nil => simp [bits]
  | cons x xs ih =>
    rw [bits,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,ih,List.mem_cons]
    constructor
    · rintro (h|h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h|h)
      · exact Or.inl h.symm
      · exact Or.inr h

def good (q : Nat) : Bool :=
  (q.testBit 5 || q.testBit 4) && (q.testBit 11 || q.testBit 10) &&
  xor (q.testBit 3) (q.testBit 9) && !(xor (q.testBit 2) (q.testBit 8))

def rowStep (a u : Nat) : Nat := ((a ^^^ ((a <<< 1) ||| (a <<< 2))) &&& 60) ||| (u % 4)
def advance (q u : Nat) : Nat := rowStep (q%64) (u%4) + 64*rowStep (q/64) (u/4)
def projection (q : Nat) : Nat := (q%64)/4 + 16*((q/64)/4)
def swap (p : Nat) : Nat := p/16 + 16*(p%16)

'''
code=[prelude]
for i,level in enumerate(levels):
    code.append(f'def level{i} : List Nat := {ls(level)}\n')
    code.append(f'def mask{i} : Nat := {mask(level)}\n')
    code.append(f'theorem mask{i}_eq : mask{i}=bits level{i} := by decide +kernel\n')
code.append('''
theorem base_check : (List.range 4096).all (fun q => !good q || mask0.testBit q)=true := by
  decide +kernel
''')
for i in range(3):
    code.append(f'''theorem prune{i}_check : level{i}.all (fun q =>
    (List.range 16).all (fun u => !(mask{i}.testBit (advance q u)) || mask{i+1}.testBit q))=true := by
  decide +kernel
''')
code.append('def successors (q : Nat) : List Nat :=\n  match q with\n')
for q in sorted(live):code.append(f'  | {q} => {ls(succ[q])}\n')
code.append('  | _ => []\n')
code.append('''theorem successors_check : level3.all (fun q =>
    (List.range 16).all (fun u => !(mask3.testBit (advance q u)) ||
      decide (advance q u ∈ successors q)))=true := by decide +kernel

def reachMask (p : Nat) : Nat :=
  match p with
''')
for p in projections:code.append(f'  | {p} => {mask(reach[p])}\n')
code.append('  | _ => 0\n')
code.append('''def Inv (p q : Nat) : Bool := (reachMask p).testBit q
def projections : List Nat := '''+ls(projections)+'''

theorem initial_check : level3.all (fun q => Inv (projection q) q)=true := by decide +kernel
theorem projection_check : level3.all (fun q => decide (projection q ∈ projections))=true := by decide +kernel

def ClosedAt (p : Nat) : Bool := level3.all (fun q =>
  !Inv p q || (successors q).all (fun r => (successors r).all (fun s => Inv p s)))
def ExcludesAt (p : Nat) : Bool := level3.all (fun q =>
  !Inv p q || decide (projection q ≠ swap p))
''')
for i,p in enumerate(projections):
    code.append(f'theorem closed_{p} : ClosedAt {p}=true := by decide +kernel\n')
    code.append(f'theorem excludes_{p} : ExcludesAt {p}=true := by decide +kernel\n')
code.append('theorem closed_check : projections.all ClosedAt=true := by\n  simp only [projections,List.all_cons,List.all_nil,'+','.join(f'closed_{p}' for p in projections)+',Bool.and_self]\n')
code.append('theorem excludes_check : projections.all ExcludesAt=true := by\n  simp only [projections,List.all_cons,List.all_nil,'+','.join(f'excludes_{p}' for p in projections)+',Bool.and_self]\n')
code.append('\nend Rule30PlateauPairCertificate\n')
(root/'Rule30PlateauPairCertificate.lean').write_text(''.join(code),encoding='utf-8')
result={'level_counts':[len(x) for x in levels],'live_states':sorted(live),
        'successors':{str(q):succ[q] for q in sorted(succ)},
        'projection_count':len(projections),'projected_even_reach_pairs':sum(map(len,reach.values())),
        'projection_even_reach':{str(p):sorted(reach[p]) for p in projections},
        'all_projected_swaps_excluded':True,'literal_row_edges_audited':256}
(root/'plateau-certificate.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k not in ['live_states','successors','projection_even_reach']}))
