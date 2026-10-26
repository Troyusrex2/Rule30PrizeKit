module
public import Rule30ReaderCanonicalResearch

/-! The sound reader extends over an equal-head cell once its prefix is
accepted and the new head agrees at times zero, one and two. This is an
all-width finite invariant; the canonical observer is not assumed proved. -/
@[expose] public section
namespace Rule30ReaderObserverReductionResearch
open Rule30ColumnReaderResearch
open Rule30ReaderCanonicalResearch
set_option maxRecDepth 30000
set_option maxHeartbeats 30000000

structure Deep where
  reader : Nat
  p0 : Symbol
  r0 : Symbol
  p1 : Symbol
  r1 : Symbol
  p2 : Symbol
  deriving DecidableEq
def initial : Deep := ⟨0,zero,zero,zero,zero,zero⟩
def advance (q : Deep) (s : Symbol) : Deep :=
  let v := update q.p0 q.r0 s
  ⟨next q.reader s,s,q.p0,v,q.p1,update q.p1 q.r1 v⟩
def deepRun (q : Deep) : List Symbol → Deep
  | [] => q
  | s::ss => deepRun (advance q s) ss
EXTENSION_DEFS
def Equal (s : Symbol) : Prop := s.1=s.2
def Good (q : Deep) (s : Symbol) : Prop :=
  accepted q.reader=true → Equal (advance q s).p0 → Equal (advance q s).p1 →
    Equal (advance q s).p2 → accepted (advance q s).reader=true
instance (q : Deep) (s : Symbol) : Decidable (Good q s) := by unfold Good Equal;infer_instance
theorem dinitial : initial∈deepAllowed := by decide +kernel
def closedTest (q : Deep) : Bool := decide (∀ x y : Bool, advance q (x,y)∈deepAllowed)
def goodTest (q : Deep) : Bool := decide (∀ x y : Bool, Good q (x,y))
EXTENSION_CHECKS
theorem deep_mem (ss : List Symbol) : ∀ q, q∈deepAllowed → deepRun q ss∈deepAllowed := by
  induction ss with
  | nil => exact fun _ h => h
  | cons s ss ih =>
    intro q h
    exact ih _ ((of_decide_eq_true (List.all_eq_true.mp dclosed_check q h)) s.1 s.2)
theorem deep_reader (ss : List Symbol) (q : Deep) : (deepRun q ss).reader=run q.reader ss := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (advance q s)
theorem deep_zero (ss : List Symbol) (q : Deep) : (deepRun q ss).p0=lastPair q.p0 ss := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (advance q s)
theorem deep_one (ss : List Symbol) (q : Deep) :
    (deepRun q ss).p1=lastPair q.p1 (change q.p0 q.r0 ss) := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (advance q s)
theorem deep_two (ss : List Symbol) (q : Deep) :
    (deepRun q ss).p2=lastPair q.p2 (change q.p1 q.r1 (change q.p0 q.r0 ss)) := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (advance q s)
theorem deep_append (ss ts : List Symbol) (q : Deep) :
    deepRun q (ss++ts)=deepRun (deepRun q ss) ts := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (advance q s)
theorem reader_append (ss ts : List Symbol) (q : Nat) : run q (ss++ts)=run (run q ss) ts := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (next q s)

theorem extension_words (ss : List Symbol) (s : Symbol)
    (hp : accepted (run 0 ss)=true)
    (h0 : Equal (lastPair zero (ss++[s])))
    (h1 : Equal (lastPair zero (stepWord (ss++[s]))))
    (h2 : Equal (lastPair zero (stepWord (stepWord (ss++[s]))))) :
    accepted (run 0 (ss++[s]))=true := by
  let q := deepRun initial ss
  have hq : q∈deepAllowed := deep_mem ss initial dinitial
  have hgood := (of_decide_eq_true (List.all_eq_true.mp good_check q hq)) s.1 s.2
  have hr : q.reader=run 0 ss := deep_reader ss initial
  have hz : (advance q s).p0=lastPair zero (ss++[s]) := by
    have h := deep_zero (ss++[s]) initial
    simpa only [deep_append,deepRun,initial,q] using h
  have ho : (advance q s).p1=lastPair zero (stepWord (ss++[s])) := by
    have h := deep_one (ss++[s]) initial
    simpa only [deep_append,deepRun,initial,stepWord,q] using h
  have ht : (advance q s).p2=lastPair zero (stepWord (stepWord (ss++[s]))) := by
    have h := deep_two (ss++[s]) initial
    simpa only [deep_append,deepRun,initial,stepWord,q] using h
  have hh := hgood (by rw [hr];exact hp) (by rw [hz];exact h0)
    (by rw [ho];exact h1) (by rw [ht];exact h2)
  change accepted (next q.reader s)=true at hh
  rw [hr] at hh
  simpa only [reader_append,run] using hh

def pairIter (ss : List Symbol) : Nat → List Symbol
  | 0 => ss
  | t+1 => stepWord (pairIter ss t)
theorem iter_length (xs : List Bool) (t : Nat) : (iter xs t).length=xs.length := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter,singleStep_length,ih]
theorem pair_iter_zip (xs ys : List Bool) (t : Nat) :
    pairIter (xs.zip ys) t=(iter xs t).zip (iter ys t) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [pairIter,ih,stepWord,change_zip,zero,iter,singleStep]
theorem trace_last (xs ys : List Bool) (hlen : xs.length=ys.length) (h : TraceEqual xs ys) (t : Nat) :
    Equal (lastPair zero (pairIter (xs.zip ys) t)) := by
  rw [pair_iter_zip,last_projection,zip_left _ _ (by rw [iter_length,iter_length];exact hlen),
    zip_right _ _ (by rw [iter_length,iter_length];exact hlen)]
  exact h t
theorem zip_snoc (xs ys : List Bool) (x y : Bool) (h : xs.length=ys.length) :
    (xs++[x]).zip (ys++[y])=(xs.zip ys)++[(x,y)] := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons u xs ih =>
    cases ys with
    | nil => simp at h
    | cons v ys => simp only [List.cons_append,List.zip_cons_cons];rw [ih ys (by simpa using h)]
theorem same_snoc (xs ys : List Bool) (x y : Bool) (hp : Same xs ys)
    (ht : TraceEqual (xs++[x]) (ys++[y])) : Same (xs++[x]) (ys++[y]) := by
  have hlen0 := hp.1
  have hlen : (xs++[x]).length=(ys++[y]).length := by simp only [List.length_append,List.length_cons,List.length_nil];omega
  refine ⟨hlen,?_⟩
  have hh := trace_last (xs++[x]) (ys++[y]) hlen ht
  rw [zip_snoc xs ys x y hp.1] at hh ⊢
  exact extension_words (xs.zip ys) (x,y) hp.2
    (by simpa only [pairIter] using hh 0)
    (by simpa only [pairIter] using hh 1)
    (by simpa only [pairIter] using hh 2)

def ParentObserver : Prop := ∀ xs ys : List Bool, ∀ x y : Bool,
  xs.length=ys.length → Canonical (xs++[x]) → Canonical (ys++[y]) →
  TraceEqual (xs++[x]) (ys++[y]) → TraceEqual xs ys
def ParentBitObserver : Prop := ∀ xs ys : List Bool, ∀ x y : Bool,
  xs.length=ys.length → Canonical (xs++[x]) → Canonical (ys++[y]) →
  TraceEqual (xs++[x]) (ys++[y]) → lastBit false xs=lastBit false ys

theorem split_last (xs : List Bool) (h : 0<xs.length) : ∃ ps x, xs=ps++[x] := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨[],x,rfl⟩
    | cons y ys =>
      obtain ⟨ps,z,hz⟩ := ih (by simp)
      exact ⟨x::ps,z,by rw [hz];rfl⟩
theorem snoc_front_unique (xs ys : List Bool) (x y : Bool)
    (h : xs++[x]=ys++[y]) : xs=ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons z zs => have hl := congrArg List.length h;simp at hl
  | cons u xs ih =>
    cases ys with
    | nil => have hl := congrArg List.length h;simp at hl
    | cons v ys =>
      have he := List.cons.inj h
      rw [he.1,ih ys he.2]

/-- Recovering the parent trace is sufficient despite non-prefix-compatible
normalization. The three-time extension certificate handles its core alias. -/
theorem parent_observer_iff : ParentObserver ↔ CanonicalObserver := by
  constructor
  · intro ho
    have aux : ∀ n : Nat, ∀ xs ys : List Bool, xs.length=n → ys.length=n →
        Canonical xs → Canonical ys → TraceEqual xs ys → xs=ys := by
      intro n
      induction n with
      | zero =>
        intro xs ys hx hy hc hd ht
        cases xs <;> cases ys <;> simp_all
      | succ n ih =>
        intro xs ys hx hy hc hd ht
        obtain ⟨ps,x,hxs⟩ := split_last xs (by omega)
        obtain ⟨qs,y,hys⟩ := split_last ys (by omega)
        subst xs;subst ys
        have hlp : ps.length=n := by simp only [List.length_append,List.length_cons,List.length_nil] at hx;omega
        have hlq : qs.length=n := by simp only [List.length_append,List.length_cons,List.length_nil] at hy;omega
        have htp := ho ps qs x y (hlp.trans hlq.symm) hc hd ht
        have hp := normal_spec ps
        have hq := normal_spec qs
        have htn : TraceEqual (normal ps) (normal qs) := by
          intro t
          exact ((same_trace _ _ hp.1) t).symm.trans ((htp t).trans ((same_trace _ _ hq.1) t))
        have he := ih (normal ps) (normal qs) (hp.1.1.symm.trans hlp)
          (hq.1.1.symm.trans hlq) hp.2 hq.2 htn
        exact same_canonical_unique _ _ hc hd
          (same_snoc ps qs x y ((same_iff_normal_eq ps qs).mpr he) ht)
    intro xs ys hlen hc hd ht
    exact aux xs.length xs ys rfl hlen.symm hc hd ht
  · intro ho xs ys x y hlen hc hd ht
    have he := ho (xs++[x]) (ys++[y]) (by simpa using hlen) hc hd ht
    have hp := snoc_front_unique xs ys x y he
    rw [hp]
    exact fun _ => rfl

theorem iter_add (xs : List Bool) (t s : Nat) : iter (iter xs t) s=iter xs (t+s) := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [iter,ih];rfl
theorem canonical_iter (xs : List Bool) (hc : Canonical xs) (t : Nat) : Canonical (iter xs t) := by
  induction t with
  | zero => exact hc
  | succ t ih => exact (canonical_step _).mp ih
theorem trace_iter (xs ys : List Bool) (h : TraceEqual xs ys) (t : Nat) :
    TraceEqual (iter xs t) (iter ys t) := by
  intro s;rw [iter_add,iter_add];exact h (t+s)
theorem change_snoc (xs : List Bool) (p q x : Bool) :
    ∃ y, singleChange p q (xs++[x])=singleChange p q xs++[y] := by
  induction xs generalizing p q with
  | nil => exact ⟨xor x (p || q),rfl⟩
  | cons s ss ih =>
    obtain ⟨y,hy⟩ := ih s p
    exact ⟨y,by simp only [List.cons_append,singleChange];rw [hy]⟩
theorem iter_snoc (xs : List Bool) (x : Bool) (t : Nat) :
    ∃ y, iter (xs++[x]) t=iter xs t++[y] := by
  induction t with
  | zero => exact ⟨x,rfl⟩
  | succ t ih =>
    obtain ⟨y,hy⟩ := ih
    obtain ⟨z,hz⟩ := change_snoc (iter xs t) false false y
    refine ⟨z,?_⟩
    simp only [iter,singleStep]
    rw [hy,hz]
theorem parent_bit_iff_parent : ParentBitObserver ↔ ParentObserver := by
  constructor
  · intro ho xs ys x y hlen hc hd ht t
    obtain ⟨u,hu⟩ := iter_snoc xs x t
    obtain ⟨v,hv⟩ := iter_snoc ys y t
    have hct := canonical_iter (xs++[x]) hc t
    have hdt := canonical_iter (ys++[y]) hd t
    have htt := trace_iter (xs++[x]) (ys++[y]) ht t
    rw [hu] at hct htt
    rw [hv] at hdt htt
    exact ho (iter xs t) (iter ys t) u v
      (by rw [iter_length,iter_length];exact hlen) hct hdt htt
  · intro ho xs ys x y hlen hc hd ht
    exact (ho xs ys x y hlen hc hd ht) 0

/-- A uniform decoder for just the penultimate initial bit on canonical words
suffices. The decoder and its existence at all widths are NOT proved here. -/
theorem parent_bit_complete_reduction : ParentBitObserver ↔ ReaderComplete :=
  parent_bit_iff_parent.trans (parent_observer_iff.trans canonical_completeness_reduction)

end Rule30ReaderObserverReductionResearch
