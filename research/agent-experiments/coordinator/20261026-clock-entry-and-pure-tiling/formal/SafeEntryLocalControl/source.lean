import SafeClockEntry

/-! Fixed six-profile countercontrol. ONLY the four newer columns obey
Rule30; the two oldest profiles are freely supplied periodic drivers.
No white-boundary ancestry or minimum-width counterexample is asserted. -/
namespace SafeEntryLocalControl
open RootEventHeight HeightOneLogic SafeClockEntry
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def code : Nat → Nat
  | 0 => 15894
  | 1 => 29669
  | 2 => 21850
  | 3 => 23210
  | 4 => 38227
  | 5 => 27309
  | _ => 0

def row (j t : Nat) : Bool := (code j).testBit (t%16)

theorem recurrence_certificate : ∀ j : Fin 4, ∀ t : Fin 16,
    row (j.val+2) (t.val+1)=xor (row (j.val+2) t.val)
      (row (j.val+1) t.val || row j.val t.val) := by decide +kernel

theorem safety_certificate : ∀ t : Fin 16,
    ¬ (row 5 t.val=false ∧ row 5 (t.val+1)=false) := by decide +kernel

theorem forbidden_certificate : ∀ j : Fin 6, ∀ t : Fin 16,
    ¬ (row j.val t.val=true ∧ row j.val (t.val+1)=true ∧ row j.val (t.val+2)=false ∧
       row j.val (t.val+3)=true ∧ row j.val (t.val+4)=true) ∧
    ¬ (row j.val t.val=false ∧ row j.val (t.val+1)=false ∧ row j.val (t.val+2)=true ∧
       row j.val (t.val+3)=false ∧ row j.val (t.val+4)=false) := by decide +kernel

theorem older_events_certificate : ∀ j : Fin 5,
    (∃ t : Fin 16, row j.val t.val=false ∧ row j.val (t.val+1)=false) ∧
    (∃ t : Fin 16, row j.val t.val=true ∧ row j.val (t.val+1)=true) := by decide +kernel

theorem alltime_recurrence (j : Fin 4) :
    Recurrence (row j.val) (row (j.val+1)) (row (j.val+2)) := by
  intro t
  have h := recurrence_certificate j ⟨t%16,Nat.mod_lt _ (by decide)⟩
  simpa only [row,Nat.add_mod,Nat.mod_mod,Bool.or_comm] using h

theorem alltime_safe : RootEventHeight.Safe (row 5) := by
  intro t
  have h := safety_certificate ⟨t%16,Nat.mod_lt _ (by decide)⟩
  simpa only [row,Nat.add_mod,Nat.mod_mod] using h

theorem parent_height_certificate :
    WH (row 3) 0=0 ∧ WH (row 3) 11=6 ∧
      WH (row 4) 3=1 ∧ WH (row 4) 14= -5 := by decide +kernel

theorem neither_parent_height_two : ¬ SpanTwo (row 3) ∧ ¬ SpanTwo (row 4) := by
  obtain ⟨h0,h11,h3,h14⟩ := parent_height_certificate
  constructor
  · rintro ⟨lo,hh⟩
    have a := hh 0
    have b := hh 11
    omega
  · rintro ⟨lo,hh⟩
    have a := hh 3
    have b := hh 14
    omega

theorem no_half_clock_pair :
    ¬ ((∀ t : Fin 16, row 3 (t.val+8)=row 3 t.val) ∧
       (∀ t : Fin 16, row 4 (t.val+8)=!row 4 t.val)) ∧
    ¬ ((∀ t : Fin 16, row 4 (t.val+8)=row 4 t.val) ∧
       (∀ t : Fin 16, row 3 (t.val+8)=!row 3 t.val)) := by decide +kernel

/-- Precisely the boundary-free statement refuted: four actual recurrences
and a Safe endpoint do not force height two at either immediate parent.
The oldest TWO histories remain arbitrary in this fixed control. -/
theorem free_boundary_control :
    (∀ j : Fin 4, Recurrence (row j.val) (row (j.val+1)) (row (j.val+2))) ∧
      RootEventHeight.Safe (row 5) ∧ ¬ SpanTwo (row 3) ∧ ¬ SpanTwo (row 4) :=
  ⟨alltime_recurrence,alltime_safe,neither_parent_height_two⟩

end SafeEntryLocalControl
