import PhysicalMixtures
import Ruliology.CellularAutomata.Rule30StripCertificates

/-! The official eventual-word interface for finite mixtures of padded blocks. -/
namespace PhysicalMixtureWord
open Ruliology.CellularAutomata Rule30StripCertificates
open PhysicalMaintenance CedarPhysicalAgeBridge PhysicalMixtures

/-- Concatenate the first r blocks, each followed by its prescribed white gap. -/
def word (u : Nat → List Bool) (q : Nat → Nat) : Nat → List Bool
  | 0 => []
  | r+1 => word u q r ++ u r ++ List.replicate (q r) false

theorem word_length (u : Nat → List Bool) (q : Nat → Nat) :
    ∀ r, (word u q r).length = offset u q r
  | 0 => rfl
  | r+1 => by simp only [word,List.length_append,List.length_replicate,word_length u q r,offset]

theorem getD_append_left (a b : List Bool) (s : Nat) (hs : s < a.length) :
    (a++b).getD s false = a.getD s false := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hs]

theorem getD_append_offset (a b : List Bool) (s : Nat) :
    (a++b).getD (a.length+s) false = b.getD s false := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : a.length ≤ a.length+s)]
  rw [show a.length+s-a.length=s by omega]

theorem padded_getD (u : List Bool) (q s : Nat) :
    (u++List.replicate q false).getD s false = u.getD s false := by
  by_cases hs : s < u.length
  · exact getD_append_left u (List.replicate q false) s hs
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : u.length ≤ s),
      List.getElem?_eq_none (by omega : u.length ≤ s),List.getElem?_replicate]
    split <;> rfl

/-- Every segment has the expected local letters at its exact offset. -/
theorem segment_getD (u : Nat → List Bool) (q : Nat → Nat) :
    ∀ r i s, i < r → s < (u i).length+q i →
      (word u q r).getD (offset u q i+s) false = (u i).getD s false := by
  intro r
  induction r with
  | zero => intro i s hi; omega
  | succ r ih =>
    intro i s hi hs
    by_cases hir : i < r
    · have hend := offset_mono u q (i+1) r (by omega)
      have hindex : offset u q i+s < offset u q r := by
        rw [offset] at hend
        omega
      rw [word,List.append_assoc,getD_append_left (word u q r)
        (u r++List.replicate (q r) false) (offset u q i+s) (by rw [word_length]; exact hindex)]
      exact ih i s hir hs
    · have he : i=r := by omega
      subst i
      rw [word,List.append_assoc,
        show offset u q r+s=(word u q r).length+s by rw [word_length],getD_append_offset]
      exact padded_getD (u r) (q r) s

/-- Official eventual repetition of the concatenation implies the exact segment schedule. -/
theorem eventuallyWord_repeats (r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hevent : EventuallyWord (word u q r)) : ∃ T, RepeatsSegments T r u q := by
  obtain ⟨T,hT⟩ := hevent
  refine ⟨T,?_⟩
  intro m i hi s hs
  have hend := offset_mono u q (i+1) r (by omega)
  have hphase : offset u q i+s < offset u q r := by
    rw [offset] at hend
    omega
  rw [hT _ (by omega),word_length,
    show T+m*offset u q r+offset u q i+s-T=offset u q i+s+m*offset u q r by omega,
    Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hphase]
  exact segment_getD u q r i s hi hs

/-- An official finite repeated word with a certified adjacent large-gap pair is excluded.
All other gaps need only the linear maintenance padding. No initial stripe is assumed. -/
theorem not_eventually_word_seed_pair (N r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hN : 1 ≤ N) (hr : 1 ≤ r)
    (hlen : ∀ i, i < r → (u i).length ≤ N)
    (hblack : ∀ i, i < r → ∃ j, j < (u i).length ∧ (u i).getD j false = true)
    (hq : ∀ i, i < r → padding N ≤ q i)
    (hbefore : warmup N ≤ q (r-1))
    (hafter : bound N+9*horizon N ≤ q 0) :
    ¬ EventuallyWord (word u q r) := by
  intro hevent
  obtain ⟨T,hdrive⟩ := eventuallyWord_repeats r u q hevent
  exact PhysicalMixtures.not_repeats_seed_pair N T r u q hN hr hlen hblack hq
    hbefore hafter hdrive

end PhysicalMixtureWord
