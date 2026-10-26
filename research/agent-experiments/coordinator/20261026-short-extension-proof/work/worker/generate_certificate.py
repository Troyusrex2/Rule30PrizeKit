"""Generate bounded concrete trajectories; Lean proves every step independently."""
from pathlib import Path
import hashlib,itertools,json,re
root=Path(__file__).resolve().parent
source=(root/'CedarSafetySoundness.lean').read_text(encoding='utf-8')
rows=re.findall(r'\| (\d+) => ⟨(\d+), ofNat (\d+), ofNat (\d+)⟩',source)
states={int(i):(int(q),int(p),int(r)) for i,q,p,r in rows}
assert len(states)==28
words=[list(xs) for length in range(4) for xs in itertools.product([0,1],repeat=length)]
def leanword(xs):return '['+','.join('true' if x else 'false' for x in xs)+']'
def bit(p,t):return (p>>(t%8))&1
def step(p,r,xs):
    out=[]
    for x in xs:
        out.append(x^(p|r));r,p=p,x
    return out
def case_type(i,k):return f'ShortOutcome (previous ⟨{i},by decide⟩) (older ⟨{i},by decide⟩) (shortWord ⟨{k},by decide⟩)'
text=['import RootShortExtensionCore','import Mathlib.Tactic.FinCases','',
      '/-! Split exact trajectory witnesses for the short-extension lemma.','Every step is proved by ordinary kernel reduction; the generator is not trusted. -/',
      'namespace RootShortExtensionCertificate','open CedarSafetySoundness CedarSafety RootShortExtensionCore',
      'set_option maxRecDepth 10000','set_option maxHeartbeats 4000000','set_option Elab.async false','',
      'def previous (i : Fin 28) : Nat → Bool := lift8 (state i).previous',
      'def older (i : Fin 28) : Nat → Bool := lift8 (state i).older',
      'def ShortOutcome (p r : Nat → Bool) (xs : List Bool) : Prop :=',
      '  driven p r 8 xs=xs ∨ ∃ t : Nat,',
      '    (driven p r t xs).getLastD (p t)=false ∧',
      '    (driven p r (t+1) xs).getLastD (p (t+1))=false','',
      'def shortWord (k : Fin 15) : List Bool :=','  match k.val with']
for k,xs in enumerate(words):text.append(f'  | {k} => {leanword(xs)}')
text+=['  | _ => []','',
'''theorem shortWord_complete (xs : List Bool) (h : xs.length ≤ 3) :
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
''']
results=[]
accepted=[]
for i,(q,p,r) in states.items():
    if q not in [1,2,3,4,5,12]:continue
    accepted.append(i)
    for k,xs in enumerate(words):
        trajectory=[xs]
        for t in range(32):trajectory.append(step(bit(p,t),bit(r,t),trajectory[-1]))
        returning=trajectory[8]==xs
        unsafe=next((t for t in range(32) if not (trajectory[t][-1] if xs else bit(p,t)) and not (trajectory[t+1][-1] if xs else bit(p,t+1))),None)
        assert returning or unsafe is not None,(i,k)
        end=8 if returning else unsafe+1
        text+=['',f'theorem case_{i}_{k} : {case_type(i,k)} := by']
        for t in range(end+1):
            target=f'  have h{t} : driven (previous ⟨{i},by decide⟩) (older ⟨{i},by decide⟩) {t} (shortWord ⟨{k},by decide⟩) = {leanword(trajectory[t])} := by'
            text.append(target)
            if t==0:text.append('    rfl')
            else:text.append(f'    rw [driven,h{t-1}]\n    rfl')
        if returning:text.append('  exact Or.inl h8')
        else:text.append(f'  refine Or.inr ⟨{unsafe},?_,?_⟩\n  · rw [h{unsafe}]; rfl\n  · rw [h{unsafe+1}]; rfl')
        results.append({'state':i,'word':xs,'return8':returning,'unsafe_pair_start':unsafe,'steps_proved':end})
(root/'RootShortExtensionCases.lean').write_text('\n'.join(text+['','end RootShortExtensionCertificate','']),encoding='utf-8')
text=['import RootShortExtensionCases','import Mathlib.Data.Fintype.Fin','',
      'namespace RootShortExtensionCertificate','open CedarSafetySoundness','',
      'theorem extension_certificate (i : Fin 28) (k : Fin 15)',
       '    (ha : accepted (state i).q=true) : ShortOutcome (previous i) (older i) (shortWord k) := by',
       '  fin_cases i']
for i in range(28):
    if i not in accepted:text+=['  · cases ha']
    else:
        text+=['  · fin_cases k']
        for k in range(15):text.append(f'    · exact case_{i}_{k}')
text+=['','end RootShortExtensionCertificate','']
(root/'RootShortExtensionCertificate.lean').write_text('\n'.join(text),encoding='utf-8')
report={'generator_not_trusted_by_Lean':True,'literal_boundary':'white ancestor profiles, existing 28-state sound certificate','accepted_prefix_states':accepted,'total_cases_including_empty':len(results),'maximum_needed_step':max(c['steps_proved'] for c in results),'returning_cases':sum(c['return8'] for c in results),'cases':results}
(root/'generated-cases.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in report.items() if k!='cases'}))
