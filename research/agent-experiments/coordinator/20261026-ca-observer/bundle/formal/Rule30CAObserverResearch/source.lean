module
public import Rule30CanonicalLanguageResearch

/-! Exact finite-tail CA observation coordinates for the canonical reader.
The two observation-separation properties defined here remain open. -/
@[expose] public section
namespace Rule30CAObserverResearch
open Rule30ReaderCanonicalResearch
open Rule30CommonPastResearch
open Rule30CanonicalLanguageResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

abbrev A := singleStep
def C (xs : List Bool) := singleChange true false xs
def T (xs : List Bool) := C (A xs)
def titer (xs : List Bool) : Nat → List Bool
  | 0 => xs
  | t+1 => T (titer xs t)
def r (xs : List Bool) := lastBit false xs
def s (xs : List Bool) := r (A xs)
def trace (xs : List Bool) (t : Nat) := r (iter xs t)
def word0 (xs : List Bool) := [true,false,false] ++ xs
def word1 (xs : List Bool) := [true,true,true] ++ A xs

def Aligned : Prop := ∀ xs ys : List Bool, xs ≠ [] → ys ≠ [] →
  (∀ t, r (titer xs t)=r (titer ys t) ∧ s (titer xs t)=s (titer ys t)) → xs=ys
def PhaseSeparated : Prop := ∀ xs ys : List Bool, xs ≠ [] → ys ≠ [] →
  ¬ (∀ t, r (titer xs t)=s (titer ys t) ∧ s (titer xs t)=r (titer ys (t+1)))

theorem C_length (xs : List Bool) : (C xs).length=xs.length := singleChange_length _ _ _
theorem T_length (xs : List Bool) : (T xs).length=xs.length := by
  rw [T,C_length,singleStep_length]
theorem titer_length (xs : List Bool) (t : Nat) : (titer xs t).length=xs.length := by
  induction t with
  | zero => rfl
  | succ t ih => rw [titer,T_length,ih]
theorem A_nonempty {xs : List Bool} (h : xs ≠ []) : A xs ≠ [] := by
  intro e
  have := singleStep_length xs
  change (A xs).length=xs.length at this
  rw [e] at this
  exact h (List.eq_nil_of_length_eq_zero this.symm)
theorem T_nonempty {xs : List Bool} (h : xs ≠ []) : T xs ≠ [] := by
  intro e
  have := T_length xs
  rw [e] at this
  exact h (List.eq_nil_of_length_eq_zero this.symm)
theorem titer_nonempty {xs : List Bool} (h : xs ≠ []) (t : Nat) : titer xs t ≠ [] := by
  intro e
  have := titer_length xs t
  rw [e] at this
  exact h (List.eq_nil_of_length_eq_zero this.symm)
theorem T_ne_self {xs : List Bool} (h : xs ≠ []) : T xs ≠ xs := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons b bs => cases b <;> simp [T,C,A,singleStep,singleChange]

def undo (p q : Bool) : List Bool → List Bool
  | [] => []
  | b::bs => let x := xor b (p || q); x :: undo x p bs
theorem change_undo (p q : Bool) (xs : List Bool) : singleChange p q (undo p q xs)=xs := by
  induction xs generalizing p q with
  | nil => rfl
  | cons b bs ih =>
      simp only [undo,singleChange]
      have hb : xor (xor b (p || q)) (p || q)=b := by cases b <;> cases p <;> cases q <;> rfl
      rw [hb,ih]
theorem A_surjective (ys : List Bool) : ∃ xs, A xs=ys :=
  ⟨undo false false ys,change_undo false false ys⟩

theorem iter_add (xs : List Bool) (m n : Nat) : iter xs (m+n)=iter (iter xs m) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg singleStep ih
theorem iter_step (xs : List Bool) (t : Nat) : iter (A xs) t=iter xs (t+1) := by
  have h := iter_add xs 1 t
  simpa only [Nat.add_comm,iter] using h.symm
theorem trace_step (xs : List Bool) (t : Nat) : trace (A xs) t=trace xs (t+1) := by
  unfold trace
  rw [iter_step]
theorem trace_iter (xs : List Bool) (m t : Nat) : trace (iter xs m) t=trace xs (t+m) := by
  unfold trace
  rw [← iter_add,Nat.add_comm]

theorem change_true (xs : List Bool) : singleChange true true xs=singleChange true false xs := by
  cases xs <;> rfl
theorem section100 (xs : List Bool) : A (word0 xs)=word1 xs := rfl
theorem section111 (xs : List Bool) : A ([true,true,true]++xs)=word0 (C xs) := by
  change true::false::false::singleChange true true xs = true::false::false::singleChange true false xs
  rw [change_true]
theorem sections (xs : List Bool) : A (word1 xs)=word0 (T xs) := section111 (A xs)
theorem iter_even_odd (xs : List Bool) (t : Nat) :
    iter (word0 xs) (2*t)=word0 (titer xs t) ∧
    iter (word0 xs) (2*t+1)=word1 (titer xs t) := by
  induction t with
  | zero => exact ⟨rfl,section100 xs⟩
  | succ t ih =>
      have he : iter (word0 xs) (2*(t+1))=word0 (titer xs (t+1)) := by
        rw [show 2*(t+1)=(2*t+1)+1 by omega,iter,ih.2]
        exact sections (titer xs t)
      refine ⟨he,?_⟩
      rw [iter,he]
      exact section100 (titer xs (t+1))

theorem last_default (xs : List Bool) (h : xs ≠ []) (a b : Bool) : lastBit a xs=lastBit b xs := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons x xs => rfl
theorem r_word0 (xs : List Bool) : r (word0 xs)=r xs := rfl
theorem r_word1 {xs : List Bool} (h : xs ≠ []) : r (word1 xs)=s xs :=
  last_default (A xs) (A_nonempty h) true false
theorem trace_even (xs : List Bool) (t : Nat) : trace (word0 xs) (2*t)=r (titer xs t) := by
  unfold trace
  rw [(iter_even_odd xs t).1,r_word0]
theorem trace_odd {xs : List Bool} (h : xs ≠ []) (t : Nat) : trace (word0 xs) (2*t+1)=s (titer xs t) := by
  unfold trace
  rw [(iter_even_odd xs t).2,r_word1 (titer_nonempty h t)]
theorem trace_word1 (xs : List Bool) (t : Nat) : trace (word1 xs) t=trace (word0 xs) (t+1) := by
  rw [← section100,trace_step]
theorem trace_T (xs : List Bool) (t : Nat) : trace (word0 (T xs)) t=trace (word0 xs) (t+2) := by
  have h : iter (word0 xs) 2=word0 (T xs) := (iter_even_odd xs 1).1
  rw [← h,trace_iter]

theorem trace_aligned_iff {xs ys : List Bool} (hx : xs ≠ []) (hy : ys ≠ []) :
    TraceEqual (word0 xs) (word0 ys) ↔
    ∀ t, r (titer xs t)=r (titer ys t) ∧ s (titer xs t)=s (titer ys t) := by
  constructor
  · intro h t
    have he : trace (word0 xs) (2*t)=trace (word0 ys) (2*t) := h (2*t)
    have ho : trace (word0 xs) (2*t+1)=trace (word0 ys) (2*t+1) := h (2*t+1)
    simpa only [trace_even,trace_odd hx,trace_odd hy] using And.intro he ho
  · intro h n
    change trace (word0 xs) n=trace (word0 ys) n
    have hr := Nat.mod_lt n (by decide : 0<2)
    by_cases hm : n%2=0
    · have hn : n=2*(n/2) := by omega
      rw [hn,trace_even,trace_even]
      exact (h _).1
    · have hn : n=2*(n/2)+1 := by omega
      rw [hn,trace_odd hx,trace_odd hy]
      exact (h _).2
theorem trace_phase_iff {xs ys : List Bool} (hx : xs ≠ []) (hy : ys ≠ []) :
    TraceEqual (word0 xs) (word1 ys) ↔
    ∀ t, r (titer xs t)=s (titer ys t) ∧ s (titer xs t)=r (titer ys (t+1)) := by
  constructor
  · intro h t
    have he : trace (word0 xs) (2*t)=trace (word1 ys) (2*t) := h (2*t)
    have ho : trace (word0 xs) (2*t+1)=trace (word1 ys) (2*t+1) := h (2*t+1)
    rw [trace_even,trace_word1,trace_odd hy] at he
    rw [trace_odd hx,trace_word1,show 2*t+1+1=2*(t+1) by omega,trace_even] at ho
    exact ⟨he,ho⟩
  · intro h n
    change trace (word0 xs) n=trace (word1 ys) n
    rw [trace_word1]
    have hr := Nat.mod_lt n (by decide : 0<2)
    by_cases hm : n%2=0
    · have hn : n=2*(n/2) := by omega
      rw [hn,trace_even,trace_odd hy]
      exact (h _).1
    · have hn : n=2*(n/2)+1 := by omega
      rw [hn,trace_odd hx,show 2*(n/2)+1+1=2*(n/2+1) by omega,trace_even]
      exact (h _).2

/- The following finite-list transport reuses the arbitrary-row dyadic
period theorem from CommonPast; it is not a uniform-in-width clock bound. -/
def takeBits (x : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n+1 => x 0 :: takeBits (fun j => x (j+1)) n
def rowStep (p q : Bool) (x : Nat → Bool) : Nat → Bool
  | 0 => xor (x 0) (p || q)
  | 1 => xor (x 1) (x 0 || p)
  | j+2 => xor (x (j+2)) (x (j+1) || x j)
theorem row_shift (p q : Bool) (x : Nat → Bool) :
    rowStep (x 0) p (fun j => x (j+1))=(fun j => rowStep p q x (j+1)) := by
  funext j
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl
theorem take_change (p q : Bool) (x : Nat → Bool) (n : Nat) :
    singleChange p q (takeBits x n)=takeBits (rowStep p q x) n := by
  induction n generalizing p q x with
  | zero => rfl
  | succ n ih => simp only [takeBits,singleChange]; rw [ih,row_shift]; rfl
theorem row_white (x : Nat → Bool) : rowStep false false x=march x := by
  funext j
  cases j with
  | zero => simp only [rowStep,march]; cases x 0 <;> rfl
  | succ j => cases j with
    | zero => simp only [rowStep,march]; cases x 0 <;> cases x 1 <;> rfl
    | succ j => rfl
theorem take_white (x : Nat → Bool) (n : Nat) : A (takeBits x n)=takeBits (march x) n := by
  rw [A,singleStep,take_change,row_white]
theorem take_initial (xs : List Bool) : takeBits (fun j => xs.getD j false) xs.length=xs := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
      change v :: takeBits (fun j => vs.getD j false) vs.length=v::vs
      rw [ih]
theorem take_congr (x y : Nat → Bool) (n : Nat) (h : ∀ j, j<n → x j=y j) : takeBits x n=takeBits y n := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
      simp only [takeBits]
      rw [h 0 (by omega),ih _ _ (fun j hj => h (j+1) (by omega))]
def full (xs : List Bool) : Nat → Nat → Bool
  | 0 => fun j => xs.getD j false
  | t+1 => march (full xs t)
theorem full_actual (xs : List Bool) : Actual (full xs) := fun _ _ => rfl
theorem prefix_full (xs : List Bool) (t : Nat) : takeBits (full xs t) xs.length=iter xs t := by
  induction t with
  | zero => exact take_initial xs
  | succ t ih =>
      change takeBits (march (full xs t)) xs.length=A (iter xs t)
      rw [← take_white,ih]
theorem raise_to {f : Nat → Bool} {j n : Nat} (hle : j≤n)
    (hp : ∀ t, f (t+2^j)=f t) : ∀ t, f (t+2^n)=f t := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => exact hp
  | succ d ih => exact raise_period (j+d) ih
theorem iter_period (xs : List Bool) (n : Nat) (hn : xs.length≤n) (t : Nat) :
    iter xs (t+2^n)=iter xs t := by
  rw [← prefix_full,← prefix_full]
  apply take_congr
  intro j hj
  exact raise_to (f := fun t => full xs t j) (by omega : j≤n) (actual_periodic (full xs) (full_actual xs) j) t
theorem trace_shift_cancel {xs ys : List Bool}
    (h : ∀ t, trace xs (t+1)=trace ys (t+1)) : TraceEqual xs ys := by
  intro t
  let n := xs.length+ys.length
  have hp : 0<2^n := Nat.pow_pos (by decide)
  have he := h (t+2^n-1)
  rw [show t+2^n-1+1=t+2^n by omega] at he
  change r (iter xs (t+2^n))=r (iter ys (t+2^n)) at he
  rw [iter_period xs n (by dsimp [n]; omega),iter_period ys n (by dsimp [n]; omega)] at he
  exact he

theorem iter_zpad (k : Nat) (xs : List Bool) (t : Nat) : iter (zpad k xs) t=zpad k (iter xs t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter,ih,singleStep_zpad]; rfl
theorem r_zpad (k : Nat) (xs : List Bool) : r (zpad k xs)=r xs := by
  induction k with
  | zero => rfl
  | succ k ih => rw [zpad_succ]; exact ih
theorem trace_zpad (k : Nat) (xs : List Bool) (t : Nat) : trace (zpad k xs) t=trace xs t := by
  unfold trace
  rw [iter_zpad,r_zpad]
theorem equal_zpad_iff (k l : Nat) (xs ys : List Bool) :
    TraceEqual (zpad k xs) (zpad l ys) ↔ TraceEqual xs ys := by
  change (∀ t, trace (zpad k xs) t=trace (zpad l ys) t) ↔ ∀ t, trace xs t=trace ys t
  simp only [trace_zpad]
theorem equal_step {xs ys : List Bool} (h : TraceEqual xs ys) : TraceEqual (A xs) (A ys) := by
  intro t
  change trace (A xs) t=trace (A ys) t
  rw [trace_step,trace_step]
  exact h (t+1)
theorem equal_symm {xs ys : List Bool} (h : TraceEqual xs ys) : TraceEqual ys xs := fun t => (h t).symm
theorem core_step (xs : List Bool) (h : Core xs) : Core (A xs) := by
  obtain ⟨k,u,hu,rfl⟩ := h
  exact ⟨k,A u,by simpa only [singleStep_length] using hu,singleStep_zpad k u⟩
theorem core_trace_two (xs : List Bool) (h : Core xs) (t : Nat) : trace xs (t+2)=trace xs t := by
  rw [← trace_iter,core_step_two xs h]
theorem core_phase0_disjoint (ha : Aligned) {xs ys : List Bool}
    (hx : xs ≠ []) (hy : Core ys) : ¬ TraceEqual (word0 xs) ys := by
  intro h
  have he : TraceEqual (word0 (T xs)) (word0 xs) := by
    intro t
    change trace (word0 (T xs)) t=trace (word0 xs) t
    rw [trace_T]
    exact (h (t+2)).trans ((core_trace_two ys hy t).trans (h t).symm)
  exact T_ne_self hx (ha (T xs) xs (T_nonempty hx) hx ((trace_aligned_iff (T_nonempty hx) hx).mp he))
theorem core_phase1_disjoint (ha : Aligned) {xs ys : List Bool}
    (hx : xs ≠ []) (hy : Core ys) : ¬ TraceEqual (word1 xs) ys := by
  intro h
  have he := equal_step h
  rw [sections] at he
  exact core_phase0_disjoint ha (T_nonempty hx) (core_step ys hy) he

theorem aligned_of_observer (ho : CanonicalObserver) : Aligned := by
  intro xs ys hx hy h
  have ht := (trace_aligned_iff hx hy).mpr h
  have he : zpad ys.length (word0 xs)=zpad xs.length (word0 ys) := by
    apply ho
    · simp [word0,zpad_length,Nat.add_comm,Nat.add_left_comm]
    · exact (canonical_phase_iff _ false xs).mpr hx
    · exact (canonical_phase_iff _ false ys).mpr hy
    · exact (equal_zpad_iff _ _ _ _).mpr ht
  exact (phase_injective he).2.2
theorem phase_separated_of_observer (ho : CanonicalObserver) : PhaseSeparated := by
  intro xs ys hx hy h
  have ht := (trace_phase_iff hx hy).mpr h
  have he : zpad ys.length (word0 xs)=zpad xs.length (word1 ys) := by
    apply ho
    · simp [word0,word1,zpad_length,singleStep_length,Nat.add_comm,Nat.add_left_comm]
    · exact (canonical_phase_iff _ false xs).mpr hx
    · exact (canonical_phase_iff _ true (A ys)).mpr (A_nonempty hy)
    · exact (equal_zpad_iff _ _ _ _).mpr ht
  exact phase_ne _ _ xs (A ys) he

theorem canonical_coordinates (xs : List Bool) (hc : Canonical xs) :
    Core xs ∨ (∃ k x, x ≠ [] ∧ xs=zpad k (word0 x)) ∨
      (∃ k x, x ≠ [] ∧ xs=zpad k (word1 x)) := by
  rcases (canonical_iff xs).mp hc with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨k,y,hy,rfl⟩ := h
    obtain ⟨x,hx⟩ := A_surjective y
    have hne : x≠[] := by intro he; subst x; exact hy hx.symm
    exact Or.inr (Or.inr ⟨k,x,hne,by rw [word1,hx]⟩)
theorem phase0_equal (ha : Aligned) {k l : Nat} {xs ys : List Bool}
    (hx : xs≠[]) (hy : ys≠[])
    (hlen : (zpad k (word0 xs)).length=(zpad l (word0 ys)).length)
    (ht : TraceEqual (zpad k (word0 xs)) (zpad l (word0 ys))) :
    zpad k (word0 xs)=zpad l (word0 ys) := by
  have he := ha xs ys hx hy ((trace_aligned_iff hx hy).mp ((equal_zpad_iff _ _ _ _).mp ht))
  subst ys
  have hk : k=l := by simpa only [zpad_length,Nat.add_right_cancel_iff] using hlen
  rw [hk]
theorem phase1_equal (ha : Aligned) {k l : Nat} {xs ys : List Bool}
    (hx : xs≠[]) (hy : ys≠[])
    (hlen : (zpad k (word1 xs)).length=(zpad l (word1 ys)).length)
    (ht : TraceEqual (zpad k (word1 xs)) (zpad l (word1 ys))) :
    zpad k (word1 xs)=zpad l (word1 ys) := by
  have hp := (equal_zpad_iff _ _ _ _).mp ht
  have hshift : ∀ t, trace (word0 xs) (t+1)=trace (word0 ys) (t+1) := by
    intro t
    rw [← trace_word1,← trace_word1]
    exact hp t
  have he := ha xs ys hx hy ((trace_aligned_iff hx hy).mp (trace_shift_cancel hshift))
  subst ys
  have hk : k=l := by simpa only [zpad_length,Nat.add_right_cancel_iff] using hlen
  rw [hk]
theorem phase01_disjoint (hp : PhaseSeparated) {k l : Nat} {xs ys : List Bool}
    (hx : xs≠[]) (hy : ys≠[]) :
    ¬ TraceEqual (zpad k (word0 xs)) (zpad l (word1 ys)) := by
  intro ht
  exact hp xs ys hx hy ((trace_phase_iff hx hy).mp ((equal_zpad_iff _ _ _ _).mp ht))

/-- Complete finite-tail observer criterion, including unequal first-black
positions, opposite phases, and the period-at-most-two canonical core.
Neither conjunct on the right is proved by this adapter. -/
theorem canonical_observer_iff : CanonicalObserver ↔ Aligned ∧ PhaseSeparated := by
  constructor
  · intro ho
    exact ⟨aligned_of_observer ho,phase_separated_of_observer ho⟩
  · rintro ⟨ha,hp⟩ xs ys hlen hcx hcy ht
    rcases canonical_coordinates xs hcx with hc | ⟨k,x,hx,rfl⟩ | ⟨k,x,hx,rfl⟩
    · rcases canonical_coordinates ys hcy with hd | ⟨l,y,hy,rfl⟩ | ⟨l,y,hy,rfl⟩
      · exact core_observe_injective xs ys hc hd hlen (ht 0) (ht 1)
      · apply False.elim
        apply core_phase0_disjoint ha hy hc
        intro t
        change trace (word0 y) t=trace xs t
        rw [← trace_zpad l]
        exact (ht t).symm
      · apply False.elim
        apply core_phase1_disjoint ha hy hc
        intro t
        change trace (word1 y) t=trace xs t
        rw [← trace_zpad l]
        exact (ht t).symm
    · rcases canonical_coordinates ys hcy with hd | ⟨l,y,hy,rfl⟩ | ⟨l,y,hy,rfl⟩
      · apply False.elim
        apply core_phase0_disjoint ha hx hd
        intro t
        change trace (word0 x) t=trace ys t
        rw [← trace_zpad k]
        exact ht t
      · exact phase0_equal ha hx hy hlen ht
      · exact False.elim (phase01_disjoint hp hx hy ht)
    · rcases canonical_coordinates ys hcy with hd | ⟨l,y,hy,rfl⟩ | ⟨l,y,hy,rfl⟩
      · apply False.elim
        apply core_phase1_disjoint ha hx hd
        intro t
        change trace (word1 x) t=trace ys t
        rw [← trace_zpad k]
        exact ht t
      · exact False.elim (phase01_disjoint hp hy hx (equal_symm ht))
      · exact phase1_equal ha hx hy hlen ht

theorem reader_complete_iff : ReaderComplete ↔ Aligned ∧ PhaseSeparated :=
  canonical_completeness_reduction.symm.trans canonical_observer_iff

end Rule30CAObserverResearch
