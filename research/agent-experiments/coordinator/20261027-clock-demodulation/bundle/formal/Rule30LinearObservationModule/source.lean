module
public import Ruliology.CellularAutomata.Rule30Prize
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A finite-dimensional two-generator observation module has at most two
independent fixed vectors. No invertibility or nilpotence is assumed. -/
@[expose] public section
namespace Rule30LinearObservationModule
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def OrbitSpan (U : V →ₗ[K] V) (a b : V) : Submodule K V :=
  Submodule.span K (Set.range (fun n : Nat => (U^[n]) a) ∪
    Set.range (fun n : Nat => (U^[n]) b))

theorem quotient_step (U : V →ₗ[K] V) (x : V) :
    (LinearMap.range (U-LinearMap.id)).mkQ (U x) =
      (LinearMap.range (U-LinearMap.id)).mkQ x := by
  apply (Submodule.Quotient.eq _).mpr
  exact ⟨x,rfl⟩

theorem quotient_iterate (U : V →ₗ[K] V) (x : V) (n : Nat) :
    (LinearMap.range (U-LinearMap.id)).mkQ ((U^[n]) x) =
      (LinearMap.range (U-LinearMap.id)).mkQ x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',quotient_step,ih]

theorem quotient_two_generated (U : V →ₗ[K] V) (a b : V)
    (hspan : OrbitSpan U a b = ⊤) :
    Submodule.span K (Set.range (fun i : Bool =>
      (LinearMap.range (U-LinearMap.id)).mkQ (if i then a else b))) = ⊤ := by
  let q := (LinearMap.range (U-LinearMap.id)).mkQ
  let S : Submodule K (V ⧸ LinearMap.range (U-LinearMap.id)) :=
    Submodule.span K (Set.range (fun i : Bool => q (if i then a else b)))
  have hmem : ∀ x, x ∈ OrbitSpan U a b → q x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨n,rfl⟩ | ⟨n,rfl⟩
        · change (LinearMap.range (U-LinearMap.id)).mkQ ((U^[n]) a) ∈ S
          rw [quotient_iterate]
          exact Submodule.subset_span ⟨true,rfl⟩
        · change (LinearMap.range (U-LinearMap.id)).mkQ ((U^[n]) b) ∈ S
          rw [quotient_iterate]
          exact Submodule.subset_span ⟨false,rfl⟩
    | zero => simpa only [map_zero] using S.zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using S.add_mem ihx ihy
    | smul c x hx ih => simpa only [map_smul] using S.smul_mem c ih
  apply top_unique
  intro z hz
  obtain ⟨x,rfl⟩ := (LinearMap.range (U-LinearMap.id)).mkQ_surjective z
  exact hmem x (by rw [hspan]; trivial)

/-- Two orbit generators bound the dimension of the fixed subspace.
The ambient space may be an invariant observation submodule itself. -/
theorem two_generated_fixed_finrank_le [FiniteDimensional K V]
    (U : V →ₗ[K] V) (a b : V) (hspan : OrbitSpan U a b = ⊤) :
    Module.finrank K (LinearMap.ker (U-LinearMap.id)) ≤ 2 := by
  have hq : Module.finrank K (V ⧸ LinearMap.range (U-LinearMap.id)) ≤ 2 := by
    simpa only [Fintype.card_bool] using
      (finrank_le_of_span_eq_top (quotient_two_generated U a b hspan))
  have hn := LinearMap.finrank_range_add_finrank_ker (U-LinearMap.id)
  have hr := (LinearMap.range (U-LinearMap.id)).finrank_quotient_add_finrank
  omega

theorem left_mem_orbitSpan (U : V →ₗ[K] V) (a b : V) : a ∈ OrbitSpan U a b :=
  Submodule.subset_span (Or.inl ⟨0,rfl⟩)
theorem right_mem_orbitSpan (U : V →ₗ[K] V) (a b : V) : b ∈ OrbitSpan U a b :=
  Submodule.subset_span (Or.inr ⟨0,rfl⟩)

theorem orbitSpan_stable (U : V →ₗ[K] V) (a b : V) {x : V}
    (hx : x ∈ OrbitSpan U a b) : U x ∈ OrbitSpan U a b := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨n,rfl⟩ | ⟨n,rfl⟩
      · exact Submodule.subset_span (Or.inl ⟨n+1,Function.iterate_succ_apply' U n a⟩)
      · exact Submodule.subset_span (Or.inr ⟨n+1,Function.iterate_succ_apply' U n b⟩)
  | zero => simpa only [map_zero] using (OrbitSpan U a b).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using (OrbitSpan U a b).add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using (OrbitSpan U a b).smul_mem c ih

def orbitOperator (U : V →ₗ[K] V) (a b : V) : OrbitSpan U a b →ₗ[K] OrbitSpan U a b where
  toFun x := ⟨U x,orbitSpan_stable U a b x.property⟩
  map_add' x y := Subtype.ext (U.map_add x y)
  map_smul' c x := Subtype.ext (U.map_smul c x)

theorem orbitOperator_iterate (U : V →ₗ[K] V) (a b : V)
    (x : OrbitSpan U a b) (n : Nat) :
    (((orbitOperator U a b)^[n]) x : V)=(U^[n]) (x : V) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      change U (((orbitOperator U a b)^[n]) x : V)=U ((U^[n]) (x : V))
      rw [ih]

theorem orbitOperator_spans (U : V →ₗ[K] V) (a b : V) :
    OrbitSpan (orbitOperator U a b) ⟨a,left_mem_orbitSpan U a b⟩
      ⟨b,right_mem_orbitSpan U a b⟩ = ⊤ := by
  let W := OrbitSpan U a b
  let S := OrbitSpan (orbitOperator U a b) ⟨a,left_mem_orbitSpan U a b⟩
    ⟨b,right_mem_orbitSpan U a b⟩
  have hmem : ∀ x (hx : x ∈ W), (⟨x,hx⟩ : W) ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨n,rfl⟩ | ⟨n,rfl⟩
        · have he : (((orbitOperator U a b)^[n]) ⟨a,left_mem_orbitSpan U a b⟩ : W) =
              ⟨(U^[n]) a,Submodule.subset_span (Or.inl ⟨n,rfl⟩)⟩ :=
            Subtype.ext (orbitOperator_iterate U a b ⟨a,left_mem_orbitSpan U a b⟩ n)
          rw [← he]
          exact Submodule.subset_span (Or.inl ⟨n,rfl⟩)
        · have he : (((orbitOperator U a b)^[n]) ⟨b,right_mem_orbitSpan U a b⟩ : W) =
              ⟨(U^[n]) b,Submodule.subset_span (Or.inr ⟨n,rfl⟩)⟩ :=
            Subtype.ext (orbitOperator_iterate U a b ⟨b,right_mem_orbitSpan U a b⟩ n)
          rw [← he]
          exact Submodule.subset_span (Or.inr ⟨n,rfl⟩)
    | zero => exact S.zero_mem
    | add x y hx hy ihx ihy => exact S.add_mem ihx ihy
    | smul c x hx ih => exact S.smul_mem c ih
  apply top_unique
  intro x hx
  exact hmem x x.property

/-- Ambient-space form: any three fixed vectors in the two-output orbit
span are linearly dependent. This is the interface for observation functions. -/
theorem not_three_fixed_independent [FiniteDimensional K V]
    (U : V →ₗ[K] V) (a b : V) (v : Fin 3 → V)
    (hm : ∀ i, v i ∈ OrbitSpan U a b) (hf : ∀ i, U (v i)=v i) :
    ¬ LinearIndependent K v := by
  intro hi
  let W := OrbitSpan U a b
  let R := orbitOperator U a b
  let z : Fin 3 → W := fun i => ⟨v i,hm i⟩
  have hz : ∀ i, z i ∈ LinearMap.ker (R-LinearMap.id) := by
    intro i
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change U (v i)-v i=0
    exact sub_eq_zero.mpr (hf i)
  let w : Fin 3 → LinearMap.ker (R-LinearMap.id) := fun i => ⟨z i,hz i⟩
  have hzi : LinearIndependent K z := LinearIndependent.of_comp W.subtype hi
  have hwi : LinearIndependent K w := LinearIndependent.of_comp (LinearMap.ker (R-LinearMap.id)).subtype hzi
  have hdim := hwi.fintype_card_le_finrank
  have hbound := two_generated_fixed_finrank_le (orbitOperator U a b)
    ⟨a,left_mem_orbitSpan U a b⟩ ⟨b,right_mem_orbitSpan U a b⟩ (orbitOperator_spans U a b)
  simp only [Fintype.card_fin] at hdim
  dsimp only [R] at hdim
  omega

end Rule30LinearObservationModule
