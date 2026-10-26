module
public import Rule30ReaderEquivalenceResearch

/-! Normal forms of the sound reader equivalence, for arbitrary word lengths.
This is not trace completeness: injectivity of traces on the canonical
language remains open. The language is 0* Sigma^{<=2} union 0*1(00|11)Sigma+.
The latter description is explanatory; the formal definition is the DFA. -/
@[expose] public section
namespace Rule30ReaderCanonicalResearch
open Rule30ColumnReaderResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

def ctable : List (List Nat) := [[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]]
def cnext (q : Nat) (x : Bool) : Nat :=
  (ctable.getD q []).getD (if x then 1 else 0) 6
def caccept (q : Nat) : Bool := q==0 || q==1 || q==2 || q==3 || q==5
def crun (q : Nat) : List Bool → Nat
  | [] => q
  | x::xs => crun (cnext q x) xs
def Canonical (xs : List Bool) : Prop := caccept (crun 0 xs)=true

abbrev Pair := Nat × Nat
def pnext (q : Pair) (s : Symbol) : Pair := (next q.1 s,cnext q.2 s.2)
def prun (q : Pair) : List Symbol → Pair
  | [] => q
  | s::ss => prun (pnext q s) ss
theorem prun_first (ss : List Symbol) (q : Pair) : (prun q ss).1=run q.1 ss := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (pnext q s)
theorem prun_second (ss : List Symbol) (q : Pair) :
    (prun q ss).2=crun q.2 (ss.map Prod.snd) := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (pnext q s)

def coverTable : List (List Pair) := COVER_STATES
def coverEdges : List (List Nat) := COVER_EDGES
def cover (i : Nat) : List Pair := coverTable.getD i []
def dnext (i : Nat) (x : Bool) : Nat :=
  (coverEdges.getD i []).getD (if x then 1 else 0) 21
def drun (i : Nat) : List Bool → Nat
  | [] => i
  | x::xs => drun (dnext i x) xs

theorem dclosed_check : (List.range 21).all
    (fun i => decide (∀ x : Bool, dnext i x<21))=true := by decide +kernel
theorem cover_lift_check : (List.range 21).all (fun i =>
    decide (∀ x : Bool, (cover (dnext i x)).all (fun q =>
      decide (∃ p∈cover i, ∃ y : Bool, pnext p (x,y)=q))=true))=true := by decide +kernel
theorem cover_accept_check : (List.range 21).all (fun i =>
    decide (∃ q∈cover i, accepted q.1=true ∧ caccept q.2=true))=true := by decide +kernel
theorem dclosed (i : Nat) (hi : i<21) (x : Bool) : dnext i x<21 :=
  (of_decide_eq_true (List.all_eq_true.mp dclosed_check i (List.mem_range.mpr hi))) x
theorem cover_lift (i : Nat) (hi : i<21) (x : Bool) (q : Pair)
    (hq : q∈cover (dnext i x)) : ∃ p∈cover i, ∃ y : Bool, pnext p (x,y)=q := by
  have h := (of_decide_eq_true (List.all_eq_true.mp cover_lift_check i (List.mem_range.mpr hi))) x
  exact of_decide_eq_true (List.all_eq_true.mp h q hq)
theorem cover_accept (i : Nat) (hi : i<21) :
    ∃ q∈cover i, accepted q.1=true ∧ caccept q.2=true :=
  of_decide_eq_true (List.all_eq_true.mp cover_accept_check i (List.mem_range.mpr hi))
theorem drun_lt (xs : List Bool) : ∀ i, i<21 → drun i xs<21 := by
  induction xs with
  | nil => exact fun _ h => h
  | cons x xs ih => intro i hi;exact ih _ (dclosed i hi x)
theorem word_lift (xs : List Bool) : ∀ i, i<21 → ∀ q∈cover (drun i xs),
    ∃ p∈cover i, ∃ ss : List Symbol, ss.map Prod.fst=xs ∧ prun p ss=q := by
  induction xs with
  | nil =>
    intro i hi q hq
    exact ⟨q,hq,[],rfl,rfl⟩
  | cons x xs ih =>
    intro i hi q hq
    obtain ⟨p,hp,ss,hxs,he⟩ := ih (dnext i x) (dclosed i hi x) q hq
    obtain ⟨p0,hp0,y,hy⟩ := cover_lift i hi x p hp
    refine ⟨p0,hp0,(x,y)::ss,?_,?_⟩
    · simp only [List.map_cons];rw [hxs]
    · simp only [prun];rw [hy];exact he

theorem canonical_exists (xs : List Bool) : ∃ ss : List Symbol,
    ss.map Prod.fst=xs ∧ Canonical (ss.map Prod.snd) ∧ accepted (run 0 ss)=true := by
  obtain ⟨q,hq,hr,hc⟩ := cover_accept (drun 0 xs) (drun_lt xs 0 (by decide))
  obtain ⟨p,hp,ss,hxs,he⟩ := word_lift xs 0 (by decide) q hq
  have hp0 : p=(0,0) := by simpa [cover,coverTable] using hp
  subst p
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  rw [prun_first] at h1
  rw [prun_second] at h2
  exact ⟨ss,hxs,by unfold Canonical;rw [h2];exact hc,by rw [h1];exact hr⟩

structure UniqueState where
  reader : Nat
  left : Nat
  right : Nat
  diff : Bool
  deriving DecidableEq
def unext (q : UniqueState) (s : Symbol) : UniqueState :=
  ⟨next q.reader s,cnext q.left s.1,cnext q.right s.2,q.diff || !(s.1==s.2)⟩
def urun (q : UniqueState) : List Symbol → UniqueState
  | [] => q
  | s::ss => urun (unext q s) ss
def uniqueAllowed : List UniqueState := UNIQUE_STATES
def uniqueInv (q : UniqueState) : Prop :=
  accepted q.reader=true → caccept q.left=true → caccept q.right=true → q.diff=false
instance (q : UniqueState) : Decidable (uniqueInv q) := by unfold uniqueInv;infer_instance
theorem uinitial : (⟨0,0,0,false⟩ : UniqueState)∈uniqueAllowed := by decide +kernel
theorem uclosed_check : uniqueAllowed.all (fun q =>
    decide (∀ x y : Bool, unext q (x,y)∈uniqueAllowed))=true := by decide +kernel
theorem uinv_check : uniqueAllowed.all (fun q => decide (uniqueInv q))=true := by decide +kernel
theorem urun_mem (ss : List Symbol) : ∀ q, q∈uniqueAllowed → urun q ss∈uniqueAllowed := by
  induction ss with
  | nil => exact fun _ h => h
  | cons s ss ih =>
    intro q h
    exact ih _ ((of_decide_eq_true (List.all_eq_true.mp uclosed_check q h)) s.1 s.2)
theorem urun_reader (ss : List Symbol) (q : UniqueState) :
    (urun q ss).reader=run q.reader ss := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (unext q s)
theorem urun_left (ss : List Symbol) (q : UniqueState) :
    (urun q ss).left=crun q.left (ss.map Prod.fst) := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (unext q s)
theorem urun_right (ss : List Symbol) (q : UniqueState) :
    (urun q ss).right=crun q.right (ss.map Prod.snd) := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih => exact ih (unext q s)
theorem urun_equal (ss : List Symbol) : ∀ q, (urun q ss).diff=false →
    q.diff=false ∧ ss.map Prod.fst=ss.map Prod.snd := by
  induction ss with
  | nil => intro q h;exact ⟨h,rfl⟩
  | cons s ss ih =>
    intro q h
    obtain ⟨hd,he⟩ := ih (unext q s) h
    have hb : q.diff=false ∧ s.1=s.2 := by
      simpa [unext,Bool.or_eq_false_iff] using hd
    exact ⟨hb.1,by simp only [List.map_cons];rw [hb.2,he]⟩
theorem canonical_unique (ss : List Symbol)
    (ha : Canonical (ss.map Prod.fst)) (hb : Canonical (ss.map Prod.snd))
    (hr : accepted (run 0 ss)=true) : ss.map Prod.fst=ss.map Prod.snd := by
  have h := of_decide_eq_true (List.all_eq_true.mp uinv_check _ (urun_mem ss _ uinitial))
  unfold uniqueInv at h
  rw [urun_reader,urun_left,urun_right] at h
  exact (urun_equal ss _ (h hr ha hb)).2

def singleChange (p q : Bool) : List Bool → List Bool
  | [] => []
  | x::xs => xor x (p || q) :: singleChange x p xs
def singleStep (xs : List Bool) := singleChange false false xs
structure TimeState where
  raw : Nat
  transformed : Nat
  previous : Bool
  older : Bool
  deriving DecidableEq
def tnext (q : TimeState) (x : Bool) : TimeState :=
  ⟨cnext q.raw x,cnext q.transformed (xor x (q.previous || q.older)),x,q.previous⟩
def trun (q : TimeState) : List Bool → TimeState
  | [] => q
  | x::xs => trun (tnext q x) xs
def timeAllowed : List TimeState := TIME_STATES
theorem tinitial : (⟨0,0,false,false⟩ : TimeState)∈timeAllowed := by decide +kernel
theorem tclosed_check : timeAllowed.all (fun q =>
    decide (∀ x : Bool, tnext q x∈timeAllowed))=true := by decide +kernel
theorem tinv_check : timeAllowed.all (fun q =>
    caccept q.raw==caccept q.transformed)=true := by decide +kernel
theorem trun_mem (xs : List Bool) : ∀ q, q∈timeAllowed → trun q xs∈timeAllowed := by
  induction xs with
  | nil => exact fun _ h => h
  | cons x xs ih =>
    intro q h
    exact ih _ ((of_decide_eq_true (List.all_eq_true.mp tclosed_check q h)) x)
theorem trun_raw (xs : List Bool) (q : TimeState) : (trun q xs).raw=crun q.raw xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons x xs ih => exact ih (tnext q x)
theorem trun_transformed (xs : List Bool) (q : TimeState) :
    (trun q xs).transformed=crun q.transformed (singleChange q.previous q.older xs) := by
  induction xs generalizing q with
  | nil => rfl
  | cons x xs ih => exact ih (tnext q x)
theorem canonical_step (xs : List Bool) : Canonical xs ↔ Canonical (singleStep xs) := by
  have h := of_decide_eq_true (List.all_eq_true.mp tinv_check _ (trun_mem xs _ tinitial))
  rw [trun_raw,trun_transformed] at h
  unfold Canonical singleStep
  rw [h]

theorem zip_projections (ss : List Symbol) :
    (ss.map Prod.fst).zip (ss.map Prod.snd)=ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [List.map_cons,List.zip_cons_cons];rw [ih]
theorem zip_left (xs ys : List Bool) (h : xs.length=ys.length) :
    (xs.zip ys).map Prod.fst=xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp only [List.map_cons,List.zip_cons_cons];rw [ih ys (by simpa using h)]
theorem zip_right (xs ys : List Bool) (h : xs.length=ys.length) :
    (xs.zip ys).map Prod.snd=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp only [List.map_cons,List.zip_cons_cons];rw [ih ys (by simpa using h)]
def Same (xs ys : List Bool) : Prop :=
  xs.length=ys.length ∧ accepted (run 0 (xs.zip ys))=true
theorem representative_exists (xs : List Bool) :
    ∃ ys, Same xs ys ∧ Canonical ys := by
  obtain ⟨ss,hx,hc,hr⟩ := canonical_exists xs
  refine ⟨ss.map Prod.snd,⟨?_,?_⟩,hc⟩
  · rw [←hx];simp
  · rw [←hx,zip_projections];exact hr
theorem zip_diagonal (xs : List Bool) : xs.zip xs=xs.map (fun x => (x,x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.zip_cons_cons,List.map_cons];rw [ih]
theorem same_refl (xs : List Bool) : Same xs xs := by
  refine ⟨rfl,?_⟩
  rw [zip_diagonal]
  exact Rule30ReaderEquivalenceResearch.reflexive_words xs
theorem zip_swap (xs ys : List Bool) :
    (xs.zip ys).map Rule30ReaderEquivalenceResearch.swap=ys.zip xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys => simp only [List.zip_cons_cons,List.map_cons,Rule30ReaderEquivalenceResearch.swap];rw [ih]
theorem same_symm (xs ys : List Bool) (h : Same xs ys) : Same ys xs := by
  refine ⟨h.1.symm,?_⟩
  have he := Rule30ReaderEquivalenceResearch.symmetric_words (xs.zip ys)
  rw [zip_swap] at he
  exact he.symm.trans h.2
theorem zip_triple (xs ys zs : List Bool) (hxy : xs.length=ys.length) (hyz : ys.length=zs.length) :
    ((xs.zip (ys.zip zs)).map Rule30ReaderEquivalenceResearch.ab=xs.zip ys) ∧
    ((xs.zip (ys.zip zs)).map Rule30ReaderEquivalenceResearch.bc=ys.zip zs) ∧
    ((xs.zip (ys.zip zs)).map Rule30ReaderEquivalenceResearch.ac=xs.zip zs) := by
  induction xs generalizing ys zs with
  | nil =>
    cases ys <;> cases zs <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hxy
    | cons y ys =>
      cases zs with
      | nil => simp at hyz
      | cons z zs =>
        obtain ⟨h1,h2,h3⟩ := ih ys zs (by simpa using hxy) (by simpa using hyz)
        simp only [List.zip_cons_cons,List.map_cons,Rule30ReaderEquivalenceResearch.ab,
          Rule30ReaderEquivalenceResearch.bc,Rule30ReaderEquivalenceResearch.ac]
        exact ⟨congrArg (List.cons (x,y)) h1,congrArg (List.cons (y,z)) h2,
          congrArg (List.cons (x,z)) h3⟩
theorem same_trans (xs ys zs : List Bool) (hxy : Same xs ys) (hyz : Same ys zs) : Same xs zs := by
  refine ⟨hxy.1.trans hyz.1,?_⟩
  obtain ⟨h1,h2,h3⟩ := zip_triple xs ys zs hxy.1 hyz.1
  have he := Rule30ReaderEquivalenceResearch.transitive_words (xs.zip (ys.zip zs))
  rw [h1,h2,h3] at he
  exact he hxy.2 hyz.2
theorem same_canonical_unique (xs ys : List Bool) (hx : Canonical xs) (hy : Canonical ys)
    (h : Same xs ys) : xs=ys := by
  have he := canonical_unique (xs.zip ys)
  rw [zip_left xs ys h.1,zip_right xs ys h.1] at he
  exact he hx hy h.2

noncomputable def normal (xs : List Bool) : List Bool := Classical.choose (representative_exists xs)
theorem normal_spec (xs : List Bool) : Same xs (normal xs) ∧ Canonical (normal xs) :=
  Classical.choose_spec (representative_exists xs)
theorem normal_unique (xs ys : List Bool) (hy : Canonical ys) (h : Same xs ys) : normal xs=ys :=
  same_canonical_unique _ _ (normal_spec xs).2 hy
    (same_trans _ _ _ (same_symm _ _ (normal_spec xs).1) h)
theorem same_iff_normal_eq (xs ys : List Bool) : Same xs ys ↔ normal xs=normal ys := by
  constructor
  · intro h
    exact normal_unique xs (normal ys) (normal_spec ys).2
      (same_trans _ _ _ h (normal_spec ys).1)
  · intro h
    have hx := (normal_spec xs).1
    rw [h] at hx
    exact same_trans _ _ _ hx (same_symm _ _ (normal_spec ys).1)

theorem singleChange_length (p q : Bool) (xs : List Bool) :
    (singleChange p q xs).length=xs.length := by
  induction xs generalizing p q with
  | nil => rfl
  | cons x xs ih => simp only [singleChange,List.length_cons];rw [ih]
theorem singleStep_length (xs : List Bool) : (singleStep xs).length=xs.length :=
  singleChange_length false false xs
theorem change_zip (p q : Symbol) (xs ys : List Bool) :
    change p q (xs.zip ys)=
      (singleChange p.1 q.1 xs).zip (singleChange p.2 q.2 ys) := by
  induction xs generalizing ys p q with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [List.zip_cons_cons,change,singleChange,update]
      rw [ih]
theorem same_step (xs ys : List Bool) (h : Same xs ys) : Same (singleStep xs) (singleStep ys) := by
  refine ⟨by rw [singleStep_length,singleStep_length];exact h.1,?_⟩
  have he := acceptance_invariant (xs.zip ys)
  simp only [stepWord,change_zip,zero] at he
  exact he.symm.trans h.2
theorem normal_step (xs : List Bool) : normal (singleStep xs)=singleStep (normal xs) :=
  normal_unique _ _ ((canonical_step _).mp (normal_spec xs).2)
    (same_step _ _ (normal_spec xs).1)

def iter (xs : List Bool) : Nat → List Bool
  | 0 => xs
  | t+1 => singleStep (iter xs t)
def lastBit (d : Bool) : List Bool → Bool
  | [] => d
  | x::xs => lastBit x xs
def TraceEqual (xs ys : List Bool) : Prop :=
  ∀ t, lastBit false (iter xs t)=lastBit false (iter ys t)
theorem last_projection (ss : List Symbol) (d : Symbol) :
    lastPair d ss=(lastBit d.1 (ss.map Prod.fst),lastBit d.2 (ss.map Prod.snd)) := by
  induction ss generalizing d with
  | nil => rfl
  | cons s ss ih => exact ih s
theorem same_iter (xs ys : List Bool) (h : Same xs ys) (t : Nat) : Same (iter xs t) (iter ys t) := by
  induction t with
  | zero => exact h
  | succ t ih => exact same_step _ _ ih
theorem same_trace (xs ys : List Bool) (h : Same xs ys) : TraceEqual xs ys := by
  intro t
  have hi := same_iter xs ys h t
  have he := accepted_last_equal ((iter xs t).zip (iter ys t)) hi.2
  rw [last_projection,zip_left _ _ hi.1,zip_right _ _ hi.1] at he
  exact he

def CanonicalObserver : Prop := ∀ xs ys : List Bool, xs.length=ys.length →
  Canonical xs → Canonical ys → TraceEqual xs ys → xs=ys
def ReaderComplete : Prop := ∀ xs ys : List Bool, xs.length=ys.length →
  (Same xs ys ↔ TraceEqual xs ys)
theorem canonical_completeness_reduction : CanonicalObserver ↔ ReaderComplete := by
  constructor
  · intro ho xs ys hlen
    constructor
    · exact same_trace xs ys
    · intro ht
      apply (same_iff_normal_eq xs ys).mpr
      have hx := normal_spec xs
      have hy := normal_spec ys
      apply ho _ _ (hx.1.1.symm.trans (hlen.trans hy.1.1)) hx.2 hy.2
      intro t
      exact ((same_trace _ _ hx.1) t).symm.trans ((ht t).trans ((same_trace _ _ hy.1) t))
  · intro hc xs ys hlen hx hy ht
    exact same_canonical_unique xs ys hx hy ((hc xs ys hlen).mpr ht)

def words : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (words n).map (false :: ·) ++ (words n).map (true :: ·)
def count (q : Nat) : Nat → Nat
  | 0 => if caccept q then 1 else 0
  | n+1 => count (cnext q false) n + count (cnext q true) n
theorem word_count (n q : Nat) :
    (words n).countP (fun xs => caccept (crun q xs))=count q n := by
  induction n generalizing q with
  | zero => simp [words,crun,count];rfl
  | succ n ih =>
    simp only [words,List.countP_append,List.countP_map,Function.comp_def,count,crun]
    rw [ih,ih]
def baseCount (q : Nat) : Nat := [4,4,4,4,8,8,0].getD q 0
theorem count_facts_check : (List.range 7).all (fun q => decide (
    count q 3=baseCount q ∧
    baseCount (cnext q false)+baseCount (cnext q true)=2*baseCount q ∧
    (∀ x : Bool, cnext q x<7)))=true := by decide +kernel
theorem count_facts (q : Nat) (hq : q<7) :
    count q 3=baseCount q ∧
    baseCount (cnext q false)+baseCount (cnext q true)=2*baseCount q ∧
    (∀ x : Bool, cnext q x<7) :=
  of_decide_eq_true (List.all_eq_true.mp count_facts_check q (List.mem_range.mpr hq))
theorem count_vector (n : Nat) : ∀ q, q<7 → count q (n+3)=2^n*baseCount q := by
  induction n with
  | zero => intro q hq;simpa using (count_facts q hq).1
  | succ n ih =>
    intro q hq
    have hf := count_facts q hq
    rw [show n+1+3=(n+3)+1 by omega,count,ih _ (hf.2.2 false),ih _ (hf.2.2 true),
      ←Nat.mul_add,hf.2.1,Nat.pow_succ,Nat.mul_assoc]
theorem canonical_count (n : Nat) :
    (words (n+3)).countP (fun xs => caccept (crun 0 xs))=2^(n+2) := by
  rw [word_count,count_vector n 0 (by decide)]
  simp [baseCount,Nat.pow_add]

end Rule30ReaderCanonicalResearch
