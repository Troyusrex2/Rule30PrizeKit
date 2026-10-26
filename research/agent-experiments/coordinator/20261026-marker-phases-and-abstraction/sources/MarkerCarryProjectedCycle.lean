import MarkerCarryAmbiguity

/-! A fixed analytic projected cycle from the preserved first-break seed.
Every node is a genuine finite-white word, but ONE projected edge switches
the hidden newest phase. This is not an actual Safe nonreturning orbit. -/
namespace MarkerCarryProjectedCycle
open CedarSafetySoundness CedarSafety MarkerCarryAmbiguity
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def code (i : Fin 8) : Nat :=
  match i.val with
  | 0 => 97
  | 1 => 103
  | 2 => 57
  | 3 => 79
  | 4 => 113
  | 5 => 23
  | 6 => 105
  | 7 => 31
  | _ => 0

def node (i : Fin 8) : List Bool := (List.range 7).map (fun j => (code i).testBit j)
def next (i : Fin 8) : Fin 8 := ⟨(i.val+1)%8,Nat.mod_lt _ (by decide)⟩

theorem projected_edges : ∀ i : Fin 8, view (F (node i))=view (node (next i)) := by decide +kernel

theorem observed_safe_edges : ∀ i : Fin 8,
    topCarry (node i)=true ∧ topCarry (F (node i))=true := by decide +kernel

theorem all_nonreturn : ∀ i : Fin 8, evolution 8 (node i)≠node i := by decide +kernel

/-- Every represented node is actually unsafe. The unsafe time is outside
the two-row edge window when that node participates in the projected cycle. -/
theorem actual_zero_events : ∀ i : Fin 8, ∃ t : Fin 16,
    newest (evolution t.val (node i))=false ∧
      newest (evolution (t.val+1) (node i))=false := by decide +kernel

theorem unique_phase_switch :
    F (node ⟨0,by decide⟩)≠node ⟨1,by decide⟩ ∧
    ∀ i : Fin 8, i.val≠0 → F (node i)=node (next i) := by decide +kernel

theorem one_lap : ∀ i : Fin 8,
    next (next (next (next (next (next (next (next i)))))))=i := by decide +kernel

/-- Existential projection admits a closed all-top-carry-one path inside
the nonreturn label. Coherence of the hidden phase across edges is essential.
No impossibility of other relational invariants is inferred. -/
theorem spurious_safe_projected_cycle :
    (∀ i : Fin 8, view (F (node i))=view (node (next i))) ∧
    (∀ i : Fin 8, topCarry (node i)=true ∧ topCarry (F (node i))=true) ∧
    (∀ i : Fin 8, evolution 8 (node i)≠node i) ∧
    (∀ i : Fin 8, ¬ Safe (node i)) := by
  refine ⟨projected_edges,observed_safe_edges,all_nonreturn,?_⟩
  intro i hs
  obtain ⟨t,h0,h1⟩ := actual_zero_events i
  exact hs t.val ⟨h0,h1⟩

end MarkerCarryProjectedCycle
