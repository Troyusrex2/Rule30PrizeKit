module

public import Ruliology.CellularAutomata.Rule30Certificates.DrivenEmptyWall

/-!
# Eventual spacings three or five in the empty-right driven gate

This is a certified forward invariant of the driven right half, not a proof
that its reconstructed left row is infinite. In particular it does not prove
`CQ01Empty`, `CQ01`, `Q01`, or any prize problem.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EmptyGateSpacingResearch

open Rule30DrivenPrefixResearch Rule30Certificates.DrivenEmptyWall
open Rule30PeriodTwoSideways Rule30SpacingRenormalizationResearch

theorem wall_trim (a : Nat) : wall (a % 2^18)=wall a := by
  unfold wall
  rw [Nat.mod_mod_of_dvd a (by decide : 65536 ∣ 2^18)]

/-- The two unseen right cells range over every possibility in `good_all`. -/
theorem wall_step (a : Nat) (ha : wall a=true) : Observe a ∧ wall (double a)=true := by
  have ht : wall (a % 262144)=true := by
    change wall (a % 2^18)=true
    rw [wall_trim]
    exact ha
  have hg := good_all (a%262144) (Nat.mod_lt _ (by decide)) ht
  refine ⟨(observe_trim a).mp hg.1,?_⟩
  have he : wall (double (a % 2^18))=wall (double a) := by
    unfold wall
    rw [← double_prefix a 16]
  rw [he] at hg
  exact hg.2

theorem white_wall : ∀ n, wall (white (146+n))=true
  | 0 => entry
  | n+1 => by
      rw [show 146+(n+1)=(146+n)+1 by omega,white]
      exact (wall_step _ (white_wall n)).2

def gate (r : Nat) : Bool := u empty (146+r)

/-- Every six-cycle window obeys the exact gate restrictions, at all later times. -/
theorem empty_windows (r : Nat) : Window gate r := by
  have ho := (wall_step _ (white_wall r)).1
  simpa only [Observe,Window,gate,Nat.zero_add,Nat.add_zero,iterate_white,white_gate,Nat.add_assoc] using ho

/-- Black gate positions are never separated by one or two cycles. -/
theorem empty_spaced : Spaced gate := by
  intro r
  exact ⟨(empty_windows r).1,(empty_windows r).2.1⟩

/-- After a black observation, the next black observation is exactly three or five cycles later. -/
theorem empty_next_gap (r : Nat) (hr : gate r=true) :
    (gate (r+3)=true ∧ gate (r+4)=false ∧ gate (r+5)=false) ∨
    (gate (r+3)=false ∧ gate (r+4)=false ∧ gate (r+5)=true) :=
  (empty_windows r).2.2.1 hr

theorem empty_no_six_white (r : Nat) :
    (gate r || gate (r+1) || gate (r+2) || gate (r+3) || gate (r+4) || gate (r+5))=true :=
  (empty_windows r).2.2.2

theorem empty_black_after (r : Nat) : ∃ s, r≤s ∧ gate s=true := by
  have h := empty_no_six_white r
  simp only [Bool.or_eq_true] at h
  rcases h with ((((ha | hb) | hc) | hd) | he) | hf
  · exact ⟨r,Nat.le_refl _,ha⟩
  · exact ⟨r+1,by omega,hb⟩
  · exact ⟨r+2,by omega,hc⟩
  · exact ⟨r+3,by omega,hd⟩
  · exact ⟨r+4,by omega,he⟩
  · exact ⟨r+5,by omega,hf⟩

/-- The previously formalized translation applies once to this actual driven gate. -/
theorem empty_reconstruction_translate (m t : Nat) :
    Rule30ZeroBoundary.recon (boundary gate) (m+9) t =
      Rule30ZeroBoundary.recon (boundary (transform gate)) (m+1) t :=
  reconstruction_translate gate empty_spaced m t

/-- The one-step reconstruction transform still cannot be iterated on this actual driven gate. -/
theorem transformed_empty_not_spaced : ¬ Spaced (transform gate) := by
  intro h
  have hz := (transform_spaced_iff gate empty_spaced).mp h
  have hw := empty_no_six_white 4
  rw [hz 0,hz 1,hz 2,hz 3,hz 4,hz 5] at hw
  contradiction

end Ruliology.CellularAutomata.Rule30EmptyGateSpacingResearch
