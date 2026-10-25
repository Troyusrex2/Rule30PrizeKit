module
public import Rule30DyadicSourceResearch
public import Ruliology.CellularAutomata.Rule30CenterRuns

/-! The complete source-echo profile is not an autonomous state for the
canonical seed orbit. Adding time, history, or other state is not excluded.
This is an obstruction to this proposed representation, not to P1. -/
@[expose] public section
namespace Rule30EchoProjectionResearch
open Ruliology.CellularAutomata Rule30Diagonals Rule30DyadicSourceResearch

def parity (r t : Nat) : List Nat → Bool
  | [] => false
  | u::us => xor (decide ((u &&& r)=u) && source (2*r) (t+u)) (parity r t us)

def channel (r t : Nat) : Bool := parity r t (List.range (r+1))
def profile (t : Nat) : Nat → Bool := fun r=>channel r t

theorem source_near_left_edge_zero (r s : Nat) (hr : 0<r) (hs : s≤r+1) :
    source (2*r) s=false := by
  by_cases hearly : s<r
  · exact source_zero_before_cone _ _ (by omega)
  by_cases heq : s=r
  · subst s
    have hright : R (2*r-1) r=true := by
      have h := D_one (r-1)
      rw [show r-1+1=r by omega] at h
      simpa [R,D,show (r:Int)-(2*r-1:Nat)=1-(r:Int) by omega] using h
    simp [source,Nat.ne_of_gt (show 0<2*r by omega),hright]
  · have heq : s=r+1 := by omega
    subst s
    have hleft : R (2*r) (r+1)=false := by
      have h := Rule30CenterRuns.D_two (r-1)
      rw [show r-1+2=r+1 by omega] at h
      change Rule30Jen.cell (r+1) (2-((r+1:Nat):Int))=false at h
      change Rule30Jen.cell (r+1) (((r+1:Nat):Int)-(2*r:Nat))=false
      rw [show ((r+1:Nat):Int)-(2*r:Nat)=2-((r+1:Nat):Int) by omega]
      exact h
    simp [source,Nat.ne_of_gt (show 0<2*r by omega),hleft]

theorem parity_zero (r t : Nat) (us : List Nat)
    (h : ∀u,u∈us → source (2*r) (t+u)=false) : parity r t us=false := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    rw [parity,h u (by simp),Bool.and_false,Bool.false_xor]
    exact ih (fun v hv=>h v (by simp [hv]))

theorem channel_zero_depth (t : Nat) : channel 0 t=true := by
  simp [channel,parity,source_outer]

theorem channel_initial_zero (r : Nat) (hr : 0<r) (t : Nat) (ht : t≤1) :
    channel r t=false := by
  apply parity_zero
  intro u hu
  have hb := List.mem_range.mp hu
  exact source_near_left_edge_zero r (t+u) hr (by omega)

theorem initial_profiles_equal : profile 0=profile 1 := by
  funext r
  by_cases hz : r=0
  · subst r; exact (channel_zero_depth 0).trans (channel_zero_depth 1).symm
  · exact (channel_initial_zero r (by omega) 0 (by omega)).trans
      (channel_initial_zero r (by omega) 1 (by omega)).symm

theorem channel_two_two : channel 2 2=true := by decide +kernel

theorem next_profiles_differ : profile 1≠profile 2 := by
  intro h
  have hb := congrArg (fun f=>f 2) h
  change channel 2 1=channel 2 2 at hb
  rw [channel_initial_zero 2 (by omega) 1 (by omega),channel_two_two] at hb
  contradiction

/-- No deterministic map of the entire infinite echo profile alone advances
all canonical seed phases by one step. This does not exclude augmented states. -/
theorem no_autonomous_profile : ¬∃ F : (Nat→Bool)→(Nat→Bool),
    ∀t,F (profile t)=profile (t+1) := by
  rintro ⟨F,hF⟩
  have h := congrArg F initial_profiles_equal
  rw [hF 0,hF 1] at h
  exact next_profiles_differ h

end Rule30EchoProjectionResearch
