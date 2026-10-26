from pathlib import Path
import re,json,hashlib
root=Path(__file__).resolve().parent
source=Path('D:/MWB/Rule30/wolfram-local/agent-seven-20261024/short-extension-root-review-20261026T1840/CedarSafetyBridge.lean')
raw=source.read_bytes();assert hashlib.sha256(raw).hexdigest()=='3aa89fd43fe2ac970b4caa7408a7fb721ada0e667c5f9550faa8ef4bc39cbdd8'
rows=re.findall(r'\| (\d+) => ⟨\d+,ofNat (\d+),ofNat (\d+)⟩',raw.decode())
states=[(int(p),int(r)) for i,p,r in rows];assert len(states)==36
words=[[],[False],[True],[False,False],[False,True],[True,False],[True,True]]
records=[];witnesses=[]
for i,(p,r) in enumerate(states):
    wi=[]
    for k,v in enumerate(words):
        cur=list(v);history=[];heights=[0];row8=None
        for t in range(33):
            b=cur[-1] if cur else bool((p>>(t%8))&1)
            history.append(b)
            if t<32:heights.append(heights[-1]+(1 if t%2==0 else -1)*(not b))
            if t==8:row8=cur[:]
            pp=bool((p>>(t%8))&1);rr=bool((r>>(t%8))&1);nxt=[]
            for a in cur:nxt.append(a^(pp or rr));rr,pp=pp,a
            cur=nxt
        returned=row8==v
        high=max(range(33),key=heights.__getitem__);low=min(range(33),key=heights.__getitem__)
        if not returned:assert heights[high]-heights[low]>2,(i,k,heights)
        wi.append((0,0) if returned else (high,low))
        records.append({'state':i,'extension':k,'word':''.join('1' if b else '0' for b in v),'return8':returned,'height_witness':wi[-1],'difference':0 if returned else heights[high]-heights[low]})
    witnesses.append(wi)
text='''import RootShortExtensionCore
import RootEventHeight

/-! A fixed finite certificate for at most two extensions of every return8
profile pair. The subsequent semantic induction is over arbitrary prefixes. -/
namespace HeightTwoNearReturn
open CedarSafetySoundness CedarSafety CedarSafetyBridge RootShortExtensionCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def whiteHeight (b : Nat → Bool) : Nat → Int
  | 0 => 0
  | t+1 => whiteHeight b t + RootEventHeight.sign t * RootEventHeight.white (b t)

def trace (p r : Nat → Bool) (xs : List Bool) (t : Nat) : Bool :=
  (driven p r t xs).getLastD (p t)

def SpanTwo (b : Nat → Bool) : Prop :=
  ∃ lo : Int, ∀ t, lo ≤ whiteHeight b t ∧ whiteHeight b t ≤ lo+2

def shortWord (k : Fin 7) : List Bool :=
  match k.val with
  | 0 => []
  | 1 => [false]
  | 2 => [true]
  | 3 => [false,false]
  | 4 => [false,true]
  | 5 => [true,false]
  | _ => [true,true]

def witness (i : Fin 36) (k : Fin 7) : Nat × Nat :=
  let row := match i.val with
'''
for i,wi in enumerate(witnesses):
    text+=f'    | {i} => ['+', '.join(f'({a},{b})' for a,b in wi)+']\n'
text+='''    | _ => []
  row.getD k.val (0,0)

def Case (i : Fin 36) (k : Fin 7) : Prop :=
  let p := lift8 (CedarSafetyBridge.state i).previous
  let r := lift8 (CedarSafetyBridge.state i).older
  let xs := shortWord k
  driven p r 8 xs = xs ∨
    2 < whiteHeight (trace p r xs) (witness i k).1 -
      whiteHeight (trace p r xs) (witness i k).2

instance (i : Fin 36) (k : Fin 7) : Decidable (Case i k) := by
  unfold Case
  infer_instance

'''
for i in range(36):text+=f'theorem case_{i} : ∀ k : Fin 7, Case ⟨{i},by decide⟩ k := by decide +kernel\n'
text+='''
theorem certificate (i : Fin 36) (k : Fin 7) : Case i k := by
  rcases i with ⟨i,hi⟩
'''
text+='  omega\n' # replaced with explicit finite dispatch below
text=text.removesuffix('  omega\n')
for i in range(35):text+=f'  by_cases h{i} : i = {i}\n  · subst i; exact case_{i} k\n'
text+='  have : i = 35 := by omega\n  subst i; exact case_35 k\n\nend HeightTwoNearReturn\n'
(root/'HeightTwoNearReturn.lean').write_text(text,encoding='utf-8')
(root/'certificate-controls.json').write_text(json.dumps({'scope':'Only the existing 36 return8 profile pairs and all seven extensions of length at most two; not a clock/width search','state_source_sha256':hashlib.sha256(raw).hexdigest(),'cases':records,'return8_count':sum(r['return8'] for r in records),'height_obstruction_count':sum(not r['return8'] for r in records)},indent=2)+'\n',encoding='utf-8')
print(json.dumps({'cases':len(records),'return8':sum(r['return8'] for r in records),'obstructions':sum(not r['return8'] for r in records)}))
