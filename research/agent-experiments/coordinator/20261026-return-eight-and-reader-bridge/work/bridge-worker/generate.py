import json,re,hashlib,shutil
from pathlib import Path
root=Path(__file__).parent
base=root.parent
source=base/'short-extension-root-review-20261026T1840/CedarSafetySoundness.lean'
raw=source.read_text(encoding='utf-8')
rows=[tuple(map(int,x)) for x in re.findall(r'\| (\d+) => ⟨(\d+), ofNat (\d+), ofNat (\d+)⟩',raw)]
assert len(rows)==28
states=[x[1:] for x in rows];ids={x:i for i,x in enumerate(states)}
prod=json.loads((root/'product.json').read_text())
rtable=[[None]*28 for _ in range(28)]
for r,qa,qb,pa,ra,pb,rb in prod['states']:
    i,j=ids[qa,pa,ra],ids[qb,pb,rb]
    assert rtable[i][j] in (None,r)
    rtable[i][j]=r
assert all(v is not None for row in rtable for v in row)
safe=[[0,1],[2,3],[4,3],[2,5],[6,6],[7,8],[9,9],[9,10],[10,10],[11,12],[12,11],[11,11],[11,11]]
def ext(p,r,v):
    y=v
    for t in range(8):
        v^=((p>>t)|(r>>t))&1;y|=v<<(t+1)
    return y
stab=[]
for q,p,r in states:
    stab.append([ids[safe[q][v],ext(p,r,v),p] if safe[q][v]!=11 else 0 for v in (0,1)])
lean='''import CedarSafetyBridge
import Rule30ColumnReaderResearch

/-! Safety completeness discharges the safe-output half of the reader's sink
separation problem. It does not discharge unsafe equal traces or any fixed
physical-center observer. All assumptions remain explicit. -/
namespace PrizeSafetyBridge
open CedarSafetySoundness CedarSafety CedarSafetyBridge
namespace R := Rule30ColumnReaderResearch
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

'''
lean+='def stable : List (List Nat) := '+str(stab).replace(' ','')+'\n'
lean+='def rtable : List (List Nat) := '+str(rtable).replace(' ','')+'\n'
lean+='''def snext (i : Fin 28) (a : Bool) : Fin 28 :=
  ⟨((stable.getD i.val []).getD (if a then 1 else 0) 0) % 28, Nat.mod_lt _ (by decide)⟩
def pairState (i j : Fin 28) : Nat := (rtable.getD i.val []).getD j.val 15

theorem single_certificate : ∀ (i : Fin 28) (a : Bool), transition (state i).q a ≠ 11 →
    (state (snext i a)).q = transition (state i).q a ∧
    (state (snext i a)).previous = nextProfile (state i).previous (state i).older a ∧
    (state (snext i a)).older = (state i).previous := by decide +kernel

def PairStep (i : Fin 28) : Prop := ∀ (j : Fin 28) (a b : Bool),
    transition (state i).q a ≠ 11 → transition (state j).q b ≠ 11 →
    R.next (pairState i j) (a,b) = pairState (snext i a) (snext j b)
instance (i : Fin 28) : Decidable (PairStep i) := by unfold PairStep;infer_instance
'''
for i in range(28):lean+=f'theorem step_{i} : PairStep ⟨{i},by decide⟩ := by decide +kernel\n'
lean+='''theorem pair_step (i : Fin 28) : PairStep i := by
  have h : i.val < 28 := i.isLt
  match i with
'''
for i in range(28):lean+=f'  | ⟨{i},_⟩ => exact step_{i}\n'
lean+='  | ⟨n+28,h⟩ => omega\n'
lean+='''
theorem output_certificate : ∀ (i j : Fin 28),
    accepted (state i).q = true → accepted (state j).q = true →
    (state i).previous = (state j).previous → R.accepted (pairState i j) = true := by
  decide +kernel

theorem accepted_profiles (ss : List R.Symbol) : ∀ i j : Fin 28,
    accepted (read (state i).q (ss.map Prod.fst)) = true →
    accepted (read (state j).q (ss.map Prod.snd)) = true →
    profileTrace (state i).previous (state i).older (ss.map Prod.fst) =
      profileTrace (state j).previous (state j).older (ss.map Prod.snd) →
    R.accepted (R.run (pairState i j) ss) = true := by
  induction ss with
  | nil => intro i j ha hb he; exact output_certificate i j ha hb he
  | cons s ss ih =>
      intro i j ha hb he
      have la : transition (state i).q s.1 ≠ 11 := by
        intro hz
        change accepted (read (transition (state i).q s.1) (ss.map Prod.fst)) = true at ha
        rw [hz,sink_read] at ha
        contradiction
      have lb : transition (state j).q s.2 ≠ 11 := by
        intro hz
        change accepted (read (transition (state j).q s.2) (ss.map Prod.snd)) = true at hb
        rw [hz,sink_read] at hb
        contradiction
      have ca := single_certificate i s.1 la
      have cb := single_certificate j s.2 lb
      have ha' : accepted (read (state (snext i s.1)).q (ss.map Prod.fst)) = true := by
        rw [ca.1];exact ha
      have hb' : accepted (read (state (snext j s.2)).q (ss.map Prod.snd)) = true := by
        rw [cb.1];exact hb
      have he' : profileTrace (state (snext i s.1)).previous (state (snext i s.1)).older (ss.map Prod.fst) =
          profileTrace (state (snext j s.2)).previous (state (snext j s.2)).older (ss.map Prod.snd) := by
        rw [ca.2.1,ca.2.2,cb.2.1,cb.2.2]
        exact he
      change R.accepted (R.run (R.next (pairState i j) s) ss) = true
      rw [pair_step i j s.1 s.2 la lb]
      exact ih (snext i s.1) (snext j s.2) ha' hb' he'

theorem profile_ext (p q : Profile)
    (h : ∀ t : Fin 9, profileAt p t.val = profileAt q t.val) : p = q := by
  have h0 := h ⟨0,by decide⟩
  have h1 := h ⟨1,by decide⟩
  have h2 := h ⟨2,by decide⟩
  have h3 := h ⟨3,by decide⟩
  have h4 := h ⟨4,by decide⟩
  have h5 := h ⟨5,by decide⟩
  have h6 := h ⟨6,by decide⟩
  have h7 := h ⟨7,by decide⟩
  have h8 := h ⟨8,by decide⟩
  cases p;cases q;simp_all [profileAt]

theorem safe_language_equal_reader (ss : List R.Symbol)
    (ha : accepted (read 0 (ss.map Prod.fst)) = true)
    (hb : accepted (read 0 (ss.map Prod.snd)) = true)
    (he : ∀ t : Fin 9, newest (evolution t.val (ss.map Prod.fst)) =
      newest (evolution t.val (ss.map Prod.snd))) :
    R.accepted (R.run 0 ss) = true := by
  have hp : profileTrace zero zero (ss.map Prod.fst) = profileTrace zero zero (ss.map Prod.snd) := by
    apply profile_ext
    intro t
    rw [trace_white _ t.val (by omega),trace_white _ t.val (by omega)]
    exact he t
  have hz : state (0 : Fin 28) = ⟨0,zero,zero⟩ := by decide +kernel
  have hr : pairState (0 : Fin 28) (0 : Fin 28) = 0 := by decide +kernel
  have h := accepted_profiles ss (0 : Fin 28) (0 : Fin 28)
  rw [hz,hr] at h
  exact h ha hb hp

/-- This is exactly the global Safe -> whole-word F^8 return premise. -/
def ReturnComplete : Prop := ∀ xs : List Bool, Safe xs → evolution 8 xs = xs

theorem safe_equal_reader (hr : ReturnComplete) (ss : List R.Symbol)
    (ha : Safe (ss.map Prod.fst))
    (he : ∀ t, newest (evolution t (ss.map Prod.fst)) = newest (evolution t (ss.map Prod.snd))) :
    R.accepted (R.run 0 ss) = true := by
  have hb : Safe (ss.map Prod.snd) := by
    intro t hbad
    exact ha t ⟨(he t).trans hbad.1,(he (t+1)).trans hbad.2⟩
  apply safe_language_equal_reader ss
  · exact (safe_return_iff_accepted _).mp ⟨ha,hr _ ha⟩
  · exact (safe_return_iff_accepted _).mp ⟨hb,hr _ hb⟩
  · intro t;exact he t.val

theorem safe_sink_separates (hr : ReturnComplete) (ss : List R.Symbol)
    (ha : Safe (ss.map Prod.fst)) (hs : R.run 0 ss = 15) :
    ∃ t, newest (evolution t (ss.map Prod.fst)) ≠ newest (evolution t (ss.map Prod.snd)) := by
  classical
  by_contra hn
  have he : ∀ t, newest (evolution t (ss.map Prod.fst)) = newest (evolution t (ss.map Prod.snd)) := by
    intro t
    by_contra h
    exact hn ⟨t,h⟩
  have h := safe_equal_reader hr ss ha he
  rw [hs] at h
  contradiction

end PrizeSafetyBridge
'''
lean=lean.replace('namespace R := Rule30ColumnReaderResearch\n','').replace('R.','Rule30ColumnReaderResearch.')
lean=lean.replace('  classical\n  by_contra hn\n','  apply Classical.byContradiction\n  intro hn\n')
lean=lean.replace('    by_contra h\n    exact hn ⟨t,h⟩','    apply Classical.byContradiction\n    intro h\n    exact hn ⟨t,h⟩')
(root/'PrizeSafetyBridge.lean').write_text(lean,encoding='utf-8')
print(json.dumps({'lean_bytes':len(lean.encode()),'closed_product_states':len(prod['states']),'transition_rows':len(stab)}))
