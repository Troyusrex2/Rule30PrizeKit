module
public import Rule30SharedTailCounterResearch

/-! Finite starts can hide a fixed nearby defect for arbitrarily long.
This refutes a background-independent defect-distance observation bound,
not a bound depending on total prefix width, and not eventual separation. -/
@[expose] public section
namespace Rule30SharedTailDelayResearch
open Ruliology.CellularAutomata
open Rule30SharedTailCounterResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def cut (x : State) (N k : Nat) : Bool := if k<N then x k else false

theorem cut_finite (x : State) (N : Nat) : Finite (cut x N) := by
  refine ⟨N,?_⟩
  intro k hk
  exact ite_eq_right (by omega)

theorem orbit_local (x y : State) (N : Nat)
    (hxy : ∀ k, k<N → x k=y k) : ∀ t k, k+2*t<N → orbit x t k=orbit y t k := by
  intro t
  induction t with
  | zero => intro k hk;exact hxy k (by omega)
  | succ t ih =>
      intro k hk
      change Rule30Jen.rule (orbit x t k) (orbit x t (k+1)) (orbit x t (k+2))=
        Rule30Jen.rule (orbit y t k) (orbit y t (k+1)) (orbit y t (k+2))
      rw [ih k (by omega),ih (k+1) (by omega),ih (k+2) (by omega)]

theorem orbit_cut (x : State) (N t k : Nat) (hk : k+2*t<N) :
    orbit (cut x N) t k=orbit x t k := by
  apply orbit_local _ _ N ?_ t k hk
  intro j hj
  exact ite_eq_left hj

theorem tail_stays_shared (x y : State) (K : Nat)
    (hxy : ∀ k, K≤k → x k=y k) : ∀ t k, K≤k → orbit x t k=orbit y t k := by
  intro t
  induction t with
  | zero => exact hxy
  | succ t ih =>
      intro k hk
      change Rule30Jen.rule (orbit x t k) (orbit x t (k+1)) (orbit x t (k+2))=
        Rule30Jen.rule (orbit y t k) (orbit y t (k+1)) (orbit y t (k+2))
      rw [ih k hk,ih (k+1) (by omega),ih (k+2) (by omega)]

theorem source_stays_opposite (x y : State) (K : Nat)
    (hxy : ∀ k, K+1≤k → x k=y k) (hd : x K≠y K) :
    ∀ t, orbit x t K≠orbit y t K := by
  intro t
  induction t with
  | zero => exact hd
  | succ t ih =>
      change Rule30Jen.rule (orbit x t K) (orbit x t (K+1)) (orbit x t (K+2))≠
        Rule30Jen.rule (orbit y t K) (orbit y t (K+1)) (orbit y t (K+2))
      rw [tail_stays_shared x y (K+1) hxy t (K+1) (by omega),
        tail_stays_shared x y (K+1) hxy t (K+2) (by omega)]
      cases hx : orbit x t K <;> cases hy : orbit y t K <;>
        cases hb : orbit y t (K+1) <;> cases hc : orbit y t (K+2) <;>
        simp_all [Rule30Jen.rule]

theorem cut_tails_shared (N : Nat) : ∀ k, 5≤k →
    cut (initial true) N k=cut (initial false) N k := by
  intro k hk
  by_cases hN : k<N
  · simp only [cut,hN,ite_true]
    exact shared_tail 0 k hk
  · simp only [cut,hN,ite_false]

/-- Total background width varies; the initial defect stays within depths 1..4. -/
theorem arbitrary_finite_delay (T : Nat) : ∃ x y : State,
    Finite x ∧ Finite y ∧
    (∀ k, 2*T+8≤k → x k=false ∧ y k=false) ∧
    (∀ k, 5≤k → x k=y k) ∧
    (∀ k, k<2*T+8 → x k=initial true k ∧ y k=initial false k) ∧
    (∀ t, orbit x t 4≠orbit y t 4) ∧
    orbit x 0 5≠orbit x 1 5 ∧
    (∀ t, t≤T → orbit x t 0=orbit y t 0) := by
  let N := 2*T+8
  let x := cut (initial true) N
  let y := cut (initial false) N
  have ht : ∀ k, 5≤k → x k=y k := cut_tails_shared N
  have hs : ∀ k, k<N → x k=initial true k ∧ y k=initial false k := by
    intro k hk
    constructor <;> exact ite_eq_left hk
  have hsource : ∀ t, orbit x t 4≠orbit y t 4 := by
    apply source_stays_opposite x y 4 ht
    rw [(hs 4 (by dsimp [N];omega)).1,(hs 4 (by dsimp [N];omega)).2]
    exact source_opposite 0
  have hneighbor : orbit x 0 5≠orbit x 1 5 := by
    rw [show orbit x 0 5=orbit (initial true) 0 5 from orbit_cut _ N 0 5 (by dsimp [N];omega),
        show orbit x 1 5=orbit (initial true) 1 5 from orbit_cut _ N 1 5 (by dsimp [N];omega)]
    exact common_neighbor_nonconstant
  have hbound : ∀ k, N≤k → x k=false ∧ y k=false := by
    intro k hk
    constructor <;> exact ite_eq_right (by omega)
  refine ⟨x,y,cut_finite _ N,cut_finite _ N,hbound,ht,hs,hsource,hneighbor,?_⟩
  intro t htT
  rw [show orbit x t 0=orbit (initial true) t 0 from orbit_cut _ N t 0 (by dsimp [N];omega),
      show orbit y t 0=orbit (initial false) t 0 from orbit_cut _ N t 0 (by dsimp [N];omega)]
  exact heads_equal t

theorem no_background_independent_bound : ¬∃ B : Nat, ∀ x y : State,
    Finite x → Finite y →
    (∀ k, 5≤k → x k=y k) →
    (∀ t, orbit x t 4≠orbit y t 4) →
    orbit x 0 5≠orbit x 1 5 →
    ∃ t, t≤B ∧ orbit x t 0≠orbit y t 0 := by
  rintro ⟨B,hB⟩
  obtain ⟨x,y,hx,hy,_,ht,_,hs,hn,he⟩ := arbitrary_finite_delay B
  obtain ⟨t,htB,hd⟩ := hB x y hx hy ht hs hn
  exact hd (he t htB)

end Rule30SharedTailDelayResearch
