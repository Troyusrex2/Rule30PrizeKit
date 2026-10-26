from pathlib import Path
import json
root=Path(__file__).resolve().parent
rows=json.loads((root/'probe.json').read_bytes())['rows']
s='''import RootShortExtensionCore

/-! Every Safe extension of at most three cells of a whole-word returning
prefix also returns after eight steps. The prefix need not itself be Safe.
The 36-pair certificate is followed by arbitrary-prefix induction. -/
namespace RootReturningPrefixSafety
open CedarSafetySoundness CedarSafety RootShortExtensionCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def shortWord (k : Fin 15) : List Bool :=
  match k.val with
'''
for k,row in enumerate(rows[:15]):
    s+=f"  | {k} => ["+','.join('true' if x else 'false' for x in row['tail'])+"]\n"
s+='''  | _ => []

theorem shortWord_complete (xs : List Bool) (h : xs.length ≤ 3) :
    ∃ k : Fin 15, shortWord k = xs := by
  cases xs with
  | nil => decide
  | cons a xs =>
    cases xs with
    | nil => cases a <;> decide
    | cons b xs =>
      cases xs with
      | nil => cases a <;> cases b <;> decide
      | cons c xs =>
        cases xs with
        | nil => cases a <;> cases b <;> cases c <;> decide
        | cons d xs => simp only [List.length_cons] at h; omega

def witness (i : Fin 36) (k : Fin 15) : Nat :=
  let row := match i.val with
'''
for i in range(36):
    s+=f"    | {i} => ["+','.join(str(r['bad00'] or 0) for r in rows[i*15:(i+1)*15])+']\n'
s+='''    | _ => []
  row.getD k.val 0

def Case (i : Fin 36) (k : Fin 15) : Prop :=
  let p := lift8 (CedarSafetyBridge.state i).previous
  let r := lift8 (CedarSafetyBridge.state i).older
  let xs := shortWord k
  driven p r 8 xs=xs ∨
    ((driven p r (witness i k) xs).getLastD (p (witness i k))=false ∧
     (driven p r (witness i k+1) xs).getLastD (p (witness i k+1))=false)

instance (i : Fin 36) (k : Fin 15) : Decidable (Case i k) := by
  unfold Case
  infer_instance

'''
for i in range(36):
    s+=f'theorem case_{i} : ∀ k : Fin 15, Case ⟨{i},by decide⟩ k := by decide +kernel\n'
s+='''
theorem certificate (i : Fin 36) (k : Fin 15) : Case i k := by
  rcases i with ⟨i,hi⟩
'''
for i in range(35):
    s+=f'  by_cases h{i} : i = {i}\n  · subst i; exact case_{i} k\n'
s+='''  have h35 : i=35 := by omega
  subst i; exact case_35 k

theorem short_case_return (i : Fin 36) (xs : List Bool) (hv : xs.length≤3)
    (hs : DrivenSafe (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) xs) :
    driven (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) 8 xs=xs := by
  obtain ⟨k,rfl⟩ := shortWord_complete xs hv
  have hc := certificate i k
  unfold Case at hc
  rcases hc with hc | hc
  · exact hc
  · exact False.elim (hs (witness i k) hc)

theorem extension_aux (u : List Bool) : ∀ (i : Fin 36) (v : List Bool),
    v.length≤3 →
    run8 (CedarSafetyBridge.state i).previous (CedarSafetyBridge.state i).older u=u →
    DrivenSafe (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) (u++v) →
    driven (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) 8 (u++v)=u++v := by
  induction u with
  | nil => intro i v hv _ hs; exact short_case_return i v hv hs
  | cons a us ih =>
    intro i v hv hret hs
    rw [run8_cons,List.cons.injEq] at hret
    have hc := CedarSafetyBridge.transition_certificate i a
    simp only [hret.1,ite_true] at hc
    obtain ⟨j,_,hp,hr⟩ := hc
    have hs' := safe_cons (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) a (us++v) hs
    rw [history_lift8 _ _ _ hret.1] at hs'
    have sub := ih j v hv
    rw [hp,hr] at sub
    have ht := sub hret.2 hs'
    rw [List.cons_append,driven_cons,history_lift8 _ _ _ hret.1,ht]
    rfl

/-- Only the prefix's return is assumed. Safety belongs to the entire word. -/
theorem returning_prefix_safe_extension (u v : List Bool)
    (hu : evolution 8 u=u) (hv : v.length≤3) (hs : Safe (u++v)) :
    evolution 8 (u++v)=u++v := by
  have hu' : run8 zero zero u=u := by rwa [run8_white]
  have hs' := white_safe (u++v) hs
  have h := extension_aux u (0 : Fin 36) v hv
  change run8 zero zero u=u → DrivenSafe (lift8 zero) (lift8 zero) (u++v) →
    driven (lift8 zero) (lift8 zero) 8 (u++v)=u++v at h
  have hr := h hu' hs'
  rwa [driven_white] at hr

end RootReturningPrefixSafety
'''
(root/'RootReturningPrefixSafety.lean').write_text(s,encoding='utf-8')
print(json.dumps({'source_bytes':len(s.encode()),'certificate_cases':540,'nonreturn_witness_max':20,'kernel_proof_pending':True}))
