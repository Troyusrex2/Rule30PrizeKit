module

public import Ruliology.CellularAutomata.Rule30TraceEdgeResearch
public import Ruliology.CellularAutomata.Rule30FiniteWhiteRuns

/-!
# Nested finite rows and the global trace question

The noncoincidence statement and ranking function below are OPEN hypotheses.
Either would exclude every eventual period. This module verifies those
implications, not the hypotheses. A sparse construction also gives arbitrarily
long coincident center prefixes with only five and three initial black cells.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PairedTraceResearch

open Rule30Jen Rule30Realization Rule30PeriodTwoSideways Rule30FiniteConfigs
open Rule30TraceEdgeResearch Rule30ZeroBoundaryBarriers

def HasRightEdge (x : Int → Bool) (hi : Int) : Prop :=
  x hi=true ∧ ∀ p, hi<p → x p=false

def Spans (x : Int → Bool) (lo hi : Int) : Prop :=
  HasLeftEdge x lo ∧ HasRightEdge x hi

/-- The inner support straddles zero and both of its edges are strictly inside. -/
def Nested (x y : Int → Bool) : Prop :=
  ∃ a b c d : Int, Spans x a d ∧ Spans y b c ∧ a<b ∧ c<d ∧ b<0 ∧ 0<c

theorem right_edge_evol {x : Int → Bool} {hi : Int}
    (hx : HasRightEdge x hi) (t : Nat) : HasRightEdge (evol x t) (hi+t) :=
  ⟨Rule30FiniteWhiteRuns.evol_right_edge hx.1 hx.2 t,
    fun p hp => Rule30FiniteDiagonals.evol_eq_false_of_gt hx.2 t p hp⟩

theorem spans_evol {x : Int → Bool} {lo hi : Int}
    (hx : Spans x lo hi) (t : Nat) : Spans (evol x t) (lo-t) (hi+t) :=
  ⟨hasLeftEdge_evol hx.1 t,right_edge_evol hx.2 t⟩

theorem nested_evol {x y : Int → Bool} (h : Nested x y) (t : Nat) :
    Nested (evol x t) (evol y t) := by
  obtain ⟨a,b,c,d,hx,hy,hab,hcd,hb,hc⟩ := h
  exact ⟨a-t,b-t,c+t,d+t,spans_evol hx t,spans_evol hy t,
    by omega,by omega,by omega,by omega⟩

/-- OPEN: this is weaker than recovering an arbitrary finite row's left edge. -/
def NestedNoncoincidence : Prop :=
  ∀ x y : Int → Bool, FinConfig x → FinConfig y → Nested x y →
    ¬ ∀ t, evol x t 0=evol y t 0

theorem nested_noncoincidence_of_edgeObservable (h : EdgeObservable) :
    NestedNoncoincidence := by
  intro x y hx hy hn he
  obtain ⟨a,b,c,d,hxsp,hysp,hab,-,-,-⟩ := hn
  have := h x y hx hy a b hxsp.1 hysp.1 he
  omega

/-- Conditional only: the hypothesis would exclude all periods and transients. -/
theorem no_eventuallyPeriodic_of_nested_noncoincidence
    (h : NestedNoncoincidence) {x : Int → Bool} (hx : FinConfig x)
    (hne : ∃ p, x p=true) : ¬ EventuallyPeriodic (fun t => evol x t 0) := by
  rintro ⟨T,P,hP,hper⟩
  obtain ⟨lo,hlo,hleft⟩ := exists_leftmost hx hne
  obtain ⟨hi,hhi,hright⟩ := Rule30FiniteWhiteRuns.exists_rightmost hx hne
  have hspan : Spans x lo hi := ⟨⟨hlo,hleft⟩,⟨hhi,hright⟩⟩
  let S := T+lo.natAbs+hi.natAbs+1
  have hS : T≤S := by dsimp [S]; omega
  have hsleft : lo-(S:Int)<0 := by dsimp [S]; omega
  have hsright : 0<hi+(S:Int) := by dsimp [S]; omega
  apply h (evol x (S+P)) (evol x S) (evol_finConfig hx _) (evol_finConfig hx _)
  · exact ⟨lo-(S+P),lo-S,hi+S,hi+(S+P),spans_evol hspan _,spans_evol hspan _,
      by omega,by omega,hsleft,hsright⟩
  · intro t
    rw [evol_restart,evol_restart,show S+P+t=(S+t)+P by omega]
    exact hper (S+t) (by omega)

/-- The exact official statement, with no bound on the period or transient. -/
theorem problem1_of_nested_noncoincidence (h : NestedNoncoincidence) :
    Rule30Prize.Problem1 := by
  have hs : FinConfig seed := ⟨0,fun p hp => by simp only [seed,decide_eq_false_iff_not]; omega⟩
  have hn : ∃ p, seed p=true := ⟨0,by decide⟩
  have he := no_eventuallyPeriodic_of_nested_noncoincidence h hs hn
  have htrace : (fun t => evol seed t 0)=Rule30Prize.center := funext (fun t => evol_seed t 0)
  unfold Rule30Prize.Problem1
  rwa [← htrace]

def FlipRanking (V : (Int → Bool) → (Int → Bool) → Nat) : Prop :=
  ∀ x y, FinConfig x → FinConfig y → Nested x y → x 0=y 0 →
    evol x 1 0=evol y 1 0 →
      V (evol x 1) (evol y 1)+(if x 0=evol x 1 0 then 0 else 1)≤V x y

private theorem antitone_nat {a : Nat → Nat} (h : ∀ t, a (t+1)≤a t)
    {n m : Nat} (hnm : n≤m) : a m≤a n := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans (h (n+d)) ih

private theorem stabilizes_nat (a : Nat → Nat) (h : ∀ t, a (t+1)≤a t) :
    ∃ T, ∀ t, T≤t → a t=a T := by
  classical
  have key : ∀ n, (∃ t, a t≤n) → ∃ T, ∀ t, T≤t → a t=a T := by
    intro n
    induction n with
    | zero =>
        rintro ⟨T,hT⟩
        refine ⟨T,fun t ht => ?_⟩
        have := antitone_nat h ht
        omega
    | succ n ih =>
        intro hex
        by_cases hn : ∃ t, a t≤n
        · exact ih hn
        · obtain ⟨T,hT⟩ := hex
          refine ⟨T,fun t ht => ?_⟩
          have hlow : n<a t := by
            by_cases hf : a t≤n
            · exact False.elim (hn ⟨t,hf⟩)
            · omega
          have hlowT : n<a T := by
            by_cases hf : a T≤n
            · exact False.elim (hn ⟨T,hf⟩)
            · omega
          have := antitone_nat h ht
          omega
  exact key (a 0) ⟨0,Nat.le_refl _⟩

/-- Color changes occur infinitely often by the kit's period-one theorem. -/
theorem nested_noncoincidence_of_flipRanking
    (V : (Int → Bool) → (Int → Bool) → Nat) (hV : FlipRanking V) :
    NestedNoncoincidence := by
  intro x y hx hy hn he
  let a : Nat → Nat := fun t => V (evol x t) (evol y t)
  have hs (t : Nat) :
      a (t+1)+(if evol x t 0=evol x (t+1) 0 then 0 else 1)≤a t := by
    have h := hV (evol x t) (evol y t) (evol_finConfig hx t) (evol_finConfig hy t)
      (nested_evol hn t) (he t) (by simpa only [evol_restart] using he (t+1))
    have hxx : evol (evol x t) 1=evol x (t+1) := funext (fun p => evol_restart x t 1 p)
    have hyy : evol (evol y t) 1=evol y (t+1) := funext (fun p => evol_restart y t 1 p)
    rw [hxx,hyy] at h
    simpa only [a,evol_restart] using h
  have hmono (t : Nat) : a (t+1)≤a t := by
    have := hs t
    split at this <;> omega
  obtain ⟨T,hT⟩ := stabilizes_nat a hmono
  have hstep (t : Nat) (ht : T≤t) : evol x (t+1) 0=evol x t 0 := by
    have h := hs t
    rw [hT (t+1) (by omega),hT t ht] at h
    by_cases hc : evol x t 0=evol x (t+1) 0
    · exact hc.symm
    · simp only [ite_eq_right hc] at h
      omega
  have hc (n : Nat) : evol x (T+n) 0=evol x T 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [show T+(n+1)=(T+n)+1 by omega,hstep (T+n) (by omega)]
        exact ih
  obtain ⟨lo,b,c,hi,hxsp,-⟩ := hn
  apply no_column_eventually_constant_finite hx ⟨lo,hxsp.1.1⟩ 0
  refine ⟨T,evol x T 0,fun t ht => ?_⟩
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le ht
  exact hc n

theorem problem1_of_flipRanking
    (V : (Int → Bool) → (Int → Bool) → Nat) (hV : FlipRanking V) :
    Rule30Prize.Problem1 :=
  problem1_of_nested_noncoincidence (nested_noncoincidence_of_flipRanking V hV)

def innerThree (p : Int) : Bool := decide (p = -1 ∨ p=0 ∨ p=1)

def outerFive (N : Nat) (p : Int) : Bool :=
  innerThree p || decide (p = -(N:Int) ∨ p=(N:Int))

theorem outer_eq_inner (N : Nat) (p : Int) (h1 : p≠-(N:Int)) (h2 : p≠(N:Int)) :
    outerFive N p=innerThree p := by simp [outerFive,h1,h2]

theorem inner_finite : FinConfig innerThree := by
  refine ⟨1,fun p hp => ?_⟩
  simp only [innerThree,decide_eq_false_iff_not]
  omega

theorem outer_finite (N : Nat) : FinConfig (outerFive N) := by
  refine ⟨N+1,fun p hp => ?_⟩
  rw [outer_eq_inner N p (by omega) (by omega)]
  simp only [innerThree,decide_eq_false_iff_not]
  omega

theorem inner_spans : Spans innerThree (-1) 1 := by
  constructor
  · refine ⟨by decide,fun p hp => ?_⟩
    simp only [innerThree,decide_eq_false_iff_not]
    omega
  · refine ⟨by decide,fun p hp => ?_⟩
    simp only [innerThree,decide_eq_false_iff_not]
    omega

theorem outer_spans (N : Nat) (hN : 2≤N) : Spans (outerFive N) (-(N:Int)) N := by
  constructor
  · refine ⟨by simp [outerFive],fun p hp => ?_⟩
    rw [outer_eq_inner N p (by omega) (by omega)]
    simp only [innerThree,decide_eq_false_iff_not]
    omega
  · refine ⟨by simp [outerFive],fun p hp => ?_⟩
    rw [outer_eq_inner N p (by omega) (by omega)]
    simp only [innerThree,decide_eq_false_iff_not]
    omega

theorem sparse_nested (H : Nat) : Nested (outerFive (H+3)) innerThree :=
  ⟨-(H+3:Int),-1,1,H+3,outer_spans _ (by omega),inner_spans,
    by omega,by omega,by decide,by decide⟩

/-- Arbitrarily long equal center prefixes need only five versus three cells. -/
theorem sparse_agreement (H t : Nat) (ht : t≤H) :
    evol (outerFive (H+3)) t 0=evol innerThree t 0 := by
  apply evol_local (a := -(H:Int)) (b := H) (x := innerThree)
  · intro p hp1 hp2
    have h1 : p≠-((H+3:Nat):Int) := by omega
    have h2 : p≠((H+3:Nat):Int) := by omega
    exact outer_eq_inner (H+3) p h1 h2
  · omega
  · omega

def BlackCountLe (x : Int → Bool) (n : Nat) : Prop :=
  ∃ ps : List Int, ps.length≤n ∧ ∀ p, x p=true → p∈ps

theorem inner_black_count : BlackCountLe innerThree 3 := by
  refine ⟨[-1,0,1],by decide,fun p hp => ?_⟩
  simpa [innerThree] using hp

theorem outer_black_count (N : Nat) : BlackCountLe (outerFive N) 5 := by
  refine ⟨[-(N:Int),-1,0,1,N],by simp,fun p hp => ?_⟩
  simp only [outerFive,innerThree,Bool.or_eq_true,decide_eq_true_eq] at hp
  rcases hp with (h|h|h)|(h|h) <;> simp [h]

/-- A uniform separation horizon cannot depend only on the two black counts. -/
theorem no_black_count_separation_bound :
    ¬ ∃ B : Nat → Nat → Nat, ∀ m n x y,
      FinConfig x → FinConfig y → Nested x y → BlackCountLe x m → BlackCountLe y n →
      ∃ t, t≤B m n ∧ evol x t 0≠evol y t 0 := by
  rintro ⟨B,hB⟩
  obtain ⟨t,ht,hd⟩ := hB 5 3 (outerFive (B 5 3+3)) innerThree
    (outer_finite _) inner_finite (sparse_nested _) (outer_black_count _) inner_black_count
  exact hd (sparse_agreement _ t ht)

def flipCount (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => flipCount f n+(if f n=f (n+1) then 0 else 1)

theorem sparse_flip_charge_bound
    (V : (Int → Bool) → (Int → Bool) → Nat) (hV : FlipRanking V) (H : Nat) :
    ∀ t, t≤H → V (evol (outerFive (H+3)) t) (evol innerThree t)+
      flipCount (fun s => evol innerThree s 0) t≤V (outerFive (H+3)) innerThree := by
  intro t
  induction t with
  | zero => intro _; exact Nat.le_refl _
  | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have h := hV (evol (outerFive (H+3)) t) (evol innerThree t)
        (evol_finConfig (outer_finite _) t) (evol_finConfig inner_finite t)
        (nested_evol (sparse_nested H) t) (sparse_agreement H t (by omega))
        (by simpa only [evol_restart] using sparse_agreement H (t+1) ht)
      have hxx : evol (evol (outerFive (H+3)) t) 1=evol (outerFive (H+3)) (t+1) :=
        funext (fun p => evol_restart _ t 1 p)
      have hyy : evol (evol innerThree t) 1=evol innerThree (t+1) :=
        funext (fun p => evol_restart _ t 1 p)
      rw [hxx,hyy] at h
      rw [sparse_agreement H t (by omega),sparse_agreement H (t+1) ht] at h
      rw [flipCount]
      omega

/-- Even a flip-only ranking needs unbounded initial values on this sparse family. -/
theorem no_uniform_sparse_flip_rank
    (V : (Int → Bool) → (Int → Bool) → Nat) (hV : FlipRanking V) :
    ¬ ∃ K, ∀ H, V (outerFive (H+3)) innerThree≤K := by
  rintro ⟨K,hK⟩
  let f : Nat → Bool := fun t => evol innerThree t 0
  have hb (t : Nat) : flipCount f t≤K := by
    have hc := sparse_flip_charge_bound V hV t t (Nat.le_refl _)
    have hk := hK t
    change V (evol (outerFive (t+3)) t) (evol innerThree t)+flipCount f t≤_ at hc
    omega
  let a : Nat → Nat := fun t => K-flipCount f t
  have hm (t : Nat) : a (t+1)≤a t := by
    dsimp [a]
    rw [flipCount]
    split <;> omega
  obtain ⟨T,hT⟩ := stabilizes_nat a hm
  have hstep (t : Nat) (ht : T≤t) : f (t+1)=f t := by
    have he : a (t+1)=a t := (hT (t+1) (by omega)).trans (hT t ht).symm
    have h0 := hb t
    have h1 := hb (t+1)
    dsimp [a] at he
    rw [flipCount] at he h1
    by_cases hf : f t=f (t+1)
    · exact hf.symm
    · simp only [ite_eq_right hf] at he h1
      omega
  have hc (n : Nat) : f (T+n)=f T := by
    induction n with
    | zero => rfl
    | succ n ih => rw [show T+(n+1)=(T+n)+1 by omega,hstep _ (by omega),ih]
  apply no_column_eventually_constant_finite inner_finite ⟨0,by decide⟩ 0
  refine ⟨T,f T,fun t ht => ?_⟩
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le ht
  exact hc n

end Ruliology.CellularAutomata.Rule30PairedTraceResearch
