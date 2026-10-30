from pathlib import Path
from collections import deque
import json
R=Path(__file__).resolve().parent
q=8;mask=255;size=256;N=size*size
adj=[[] for _ in range(N)];rev=[[] for _ in range(N)]
for a in range(size):
    for b in range(size):
        f=a|b
        if f.bit_count()%2:continue
        u=f
        for s in [1,2,4]:u^=u<<s
        c=(u<<1)&mask;i=a*size+b
        for cc in [c,c^mask]:
            j=b*size+cc;adj[i].append(j);rev[j].append(i)
degree=list(map(len,rev));alive=bytearray([1])*N
todo=deque(i for i in range(N) if not degree[i])
while todo:
    i=todo.popleft()
    if not alive[i]:continue
    alive[i]=0
    for j in adj[i]:
        degree[j]-=1
        if alive[j] and not degree[j]:todo.append(j)
starts=[21*256+21,150*256+21]
nodes=[];index={};nxt={}
for initial in starts:
    here=initial
    while here not in index:
        index[here]=len(nodes);nodes.append(here)
        older=next(j for j in rev[here] if alive[j]);nxt[here]=older;here=older
assert all(nxt[i] in index for i in nodes)
labels=[i%256 for i in nodes];nexts=[index[nxt[i]] for i in nodes]
assert all(labels)
K=len(nodes);sa,sb=map(index.get,starts)
data={'labels':labels,'next':nexts,'startA':sa,'startB':sb,'node_pairs':[divmod(i,256) for i in nodes]}
(R/'boundary-countermodel-data.json').write_text(json.dumps(data,indent=2)+'\n')
source='''module
public import Ruliology.CellularAutomata.Rule30Prize
/-!
# Why temporal-profile decoding needs the finite white spatial boundary

Two explicit infinite spatial pasts have the same final profile, of dyadic
period8 and not periods1,2,4, but different immediate predecessors. Every
profile has period8 and the literal right-diagonal Rule30 recurrence holds.
There is no white profile anywhere in either past. This is NOT a countermodel
to white-root predecessor uniqueness, to a finite-seed theorem, or to a prize.
The finite presentation is checked; arbitrary past depth follows by iteration.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30BoundaryProfileCounterexample
open Rule30Jen

abbrev State := Fin __K__
def code (i : State) : Nat := (__LABELS__ : List Nat).getD i.val 0
def older (i : State) : State := (__NEXT__ : List State).getD i.val 0
def word (w t : Nat) : Bool := w.testBit (t%8)
def walk (i : State) : Nat → State
  | 0 => i
  | k+1 => older (walk i k)
def past (i : State) (k t : Nat) : Bool := word (code (walk i k)) t
def startA : State := __SA__
def startB : State := __SB__

theorem local_certificate : ∀ i : State, ∀ t : Fin 8,
    word (code i) (t.val+1)=xor (word (code i) t.val)
      (word (code (older i)) t.val || word (code (older (older i))) t.val) := by decide +kernel

theorem period_eight (i : State) (k t : Nat) : past i k (t+8)=past i k t := by
  simp [past,word]

/-- The exact sideways recurrence at every depth and every time. -/
theorem recurrence (i : State) (k t : Nat) :
    past i k (t+1)=xor (past i k t) (past i (k+1) t || past i (k+2) t) := by
  have h := local_certificate (walk i k) ⟨t%8,Nat.mod_lt t (by decide)⟩
  simpa [past,walk,word,Nat.add_mod] using h

theorem no_white_profile (i : State) (k : Nat) : ∃ t, past i k t=true := by
  have h : ∀ i : State, ∃ t : Fin 8, word (code i) t.val=true := by decide +kernel
  obtain ⟨t,ht⟩ := h (walk i k)
  exact ⟨t.val,ht⟩

theorem same_final : ∀ t, past startA 0 t=past startB 0 t := by
  intro t
  rfl

theorem different_predecessor : past startA 1 ≠ past startB 1 := by
  intro h
  have ht := congrFun h 0
  have hn : past startA 1 0 ≠ past startB 1 0 := by decide +kernel
  exact hn ht

theorem final_not_period_one : ¬ (∀ t, past startA 0 (t+1)=past startA 0 t) := by
  intro h
  have ht := h 0
  have hn : past startA 0 1 ≠ past startA 0 0 := by decide +kernel
  exact hn ht

theorem final_not_period_two : ¬ (∀ t, past startA 0 (t+2)=past startA 0 t) := by
  intro h
  have ht := h 4
  have hn : past startA 0 6 ≠ past startA 0 4 := by decide +kernel
  exact hn ht

theorem final_not_period_four : ¬ (∀ t, past startA 0 (t+4)=past startA 0 t) := by
  intro h
  have ht := h 2
  have hn : past startA 0 6 ≠ past startA 0 2 := by decide +kernel
  exact hn ht

/-- Infinite temporal-profile pasts need not have unique predecessors, even
when their common final profile is nonconstant and nonalternating. -/
theorem two_infinite_pasts_same_nonalt_final :
    ∃ A B : Nat → Nat → Bool,
      (∀ k t, A k (t+8)=A k t ∧ B k (t+8)=B k t) ∧
      (∀ k t, A k (t+1)=xor (A k t) (A (k+1) t || A (k+2) t)) ∧
      (∀ k t, B k (t+1)=xor (B k t) (B (k+1) t || B (k+2) t)) ∧
      (∀ t, A 0 t=B 0 t) ∧ A 1 ≠ B 1 ∧
      ¬ (∀ t, A 0 (t+1)=A 0 t) ∧ ¬ (∀ t, A 0 (t+2)=A 0 t) ∧
      ¬ (∀ t, A 0 (t+4)=A 0 t) ∧
      (∀ k, ∃ t, A k t=true) ∧ (∀ k, ∃ t, B k t=true) := by
  exact ⟨past startA,past startB,
    fun k t => ⟨period_eight startA k t,period_eight startB k t⟩,
    recurrence startA,recurrence startB,same_final,different_predecessor,
    final_not_period_one,final_not_period_two,final_not_period_four,
    no_white_profile startA,no_white_profile startB⟩

end Ruliology.CellularAutomata.Rule30BoundaryProfileCounterexample
'''
for a,b in {'__K__':str(K),'__LABELS__':str(labels),'__NEXT__':str(nexts),'__SA__':str(sa),'__SB__':str(sb)}.items():source=source.replace(a,b)
(R/'proof/BoundaryProfileCounterexample.lean').write_text(source,encoding='utf-8',newline='\n')
print('finite_presentation_states',K,'labels',labels,'starts',sa,sb)
