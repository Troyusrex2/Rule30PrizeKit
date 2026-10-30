module
public import WordBoundary
public import RankEscape
@[expose] public section
namespace MemorySeparation
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration ReturnActions ReturnSections WordBoundary RankEscape
open ReturnSections.State

theorem memory_first (a b c d : Bool) (eq : memory a b=memory c d) : a=c := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [memory]

/-- Actual equal return words determine one more full column than the cut:
the leading bit of the categorical memory is visible without masking. -/
theorem exact_tail_and_one (n P : Nat) (hn : 2≤n) (hP : 0<P) (x y z : Code)
    (fx : AgreeBelow n (iter P x) x) (fy : AgreeBelow n (iter P y) y)
    (eq : returnWord n P x=returnWord n P y) :
    ∀ t k,n-1≤k → iter t (join n x z) k=iter t (join n y z) k := by
  have tails:=shared_words_confine_at_cut n P hP x y z fx fy eq
  have states:=memory_equal_all n P hP x y fx fy eq
  intro t k hk
  by_cases high : n≤k
  · have h:=congrFun (tails t) (k-n)
    have idx : n+(k-n)=k := by omega
    simpa only [drop,idx] using h
  · have idx : k=n-1 := by omega
    subst k
    have state : stateAfter A (iter t (join n x z)) n=
        stateAfter A (iter t (join n y z)) n :=
      (joined_memory n x z t).trans ((states t).trans (joined_memory n y z t).symm)
    obtain ⟨j,rfl⟩ : ∃ j,n=j+2 := ⟨n-2,by omega⟩
    rw [after_two,after_two] at state
    exact memory_first _ _ _ _ state

/-- A genuine source-word collision must hide at least five defect digits
below its last fully observed memory bit. In particular, the new all-depth
four-layer result rules out collisions whose first difference is too close
to the interface. This is not full word injectivity. -/
theorem source_collision_separation (n P i : Nat) (hP : 0<P) (hi : 0<i) (hin : i<n)
    (x y : Code) (hx : x 0=true)
    (fx : AgreeBelow n (iter P x) x) (fy : AgreeBelow n (iter P y) y)
    (low : AgreeBelow i x y) (different : x i≠y i)
    (eq : returnWord n P x=returnWord n P y) : i+6≤n := by
  apply Classical.byContradiction
  intro close
  let u:=join n x zero
  let v:=join n y zero
  have lowuv : AgreeBelow i u v := by
    intro j hj
    exact (join_low n x zero j (by omega)).trans ((low j hj).trans (join_low n y zero j (by omega)).symm)
  have diffuv : u i≠v i := by
    simpa only [u,v,join_low n x zero i hin,join_low n y zero i hin] using different
  have edge : u 0=true := (join_low n x zero 0 (by omega)).trans hx
  have outside:=exact_tail_and_one n P (by omega) hP x y zero fx fy eq
  obtain ⟨j,rfl⟩ : ∃ j,i=j+1 := ⟨i-1,by omega⟩
  obtain ⟨t,ht,ne⟩:=four_layer_escape j u v edge lowuv diffuv
  exact ne.elim (fun h => h (outside t (j+5) (by omega)))
    (fun h => h (outside t (j+6) (by omega)))

end MemorySeparation
