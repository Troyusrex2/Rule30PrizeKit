import HeightTwoDescent

/-! Exact free-boundary obstruction to a local height-two parent alternative.
Only the oldest two temporal profiles are free. Every supplied column avoids
the four indicated forbidden cylinders, and five update equations plus six
adjacent cover relations hold for all time. No finite-white anchor is supplied
or asserted. The SMT solver was used only to find these fixed integer masks;
every claim below is independently replayed by Lean's kernel. -/
namespace HeightTwoMixedControl
open RootEventHeight HeightTwoNearReturn HeightTwoDescent
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def mask : Fin 7 → Nat
  | ⟨0,_⟩ => 2572815714
  | ⟨1,_⟩ => 3920235100
  | ⟨2,_⟩ => 2930510420
  | ⟨3,_⟩ => 3040087144
  | ⟨4,_⟩ => 3576171432
  | ⟨5,_⟩ => 2787642032
  | ⟨6,_⟩ => 1513098543

def col (i : Fin 7) (t : Nat) : Bool := (mask i).testBit (t%32)

def No00 (b : Nat → Bool) : Prop := ∀ t, ¬ (b t=false ∧ b (t+1)=false)
def No11 (b : Nat → Bool) : Prop := ∀ t, ¬ (b t=true ∧ b (t+1)=true)

def equations (t : Nat) : Prop := ∀ i : Fin 5,
  xor (col ⟨i.val+2,by omega⟩ t) (col ⟨i.val+2,by omega⟩ (t+1))=
    (col ⟨i.val+1,by omega⟩ t || col ⟨i.val,by omega⟩ t)

def covers (t : Nat) : Prop := ∀ i : Fin 6,
  (col ⟨i.val,by omega⟩ t=true →
    xor (col ⟨i.val+1,by omega⟩ t) (col ⟨i.val+1,by omega⟩ (t+1))=true) ∧
  (xor (col ⟨i.val+1,by omega⟩ t) (col ⟨i.val+1,by omega⟩ (t+1))=true →
    (col ⟨i.val,by omega⟩ t || col ⟨i.val,by omega⟩ (t+1))=true)

def cylinders (t : Nat) : Prop := ∀ i : Fin 7,
  ¬ (col i t=true ∧ col i (t+1)=true ∧ col i (t+2)=false ∧
    col i (t+3)=true ∧ col i (t+4)=true) ∧
  ¬ (col i t=false ∧ col i (t+1)=false ∧ col i (t+2)=true ∧
    col i (t+3)=false ∧ col i (t+4)=false) ∧
  ¬ (col i t=false ∧ col i (t+1)=false ∧ col i (t+2)=false ∧
    col i (t+3)=true ∧ col i (t+4)=true ∧ col i (t+5)=true) ∧
  ¬ (col i t=true ∧ col i (t+1)=true ∧ col i (t+2)=true ∧
    col i (t+3)=false ∧ col i (t+4)=false ∧ col i (t+5)=false)

theorem local_certificate : ∀ t : Fin 32,
    equations t.val ∧ covers t.val ∧ cylinders t.val := by decide +kernel

theorem all_time_local_constraints (t : Nat) : equations t ∧ covers t ∧ cylinders t := by
  have h := local_certificate ⟨t%32,by omega⟩
  simpa [equations,covers,cylinders,col,Nat.add_mod] using h

theorem periodic (i : Fin 7) : HeightOneLogic.Periodic (col i) 32 := by
  intro t
  simp [col,Nat.add_mod]

theorem height_certificate : whiteHeight (col 6) 32=0 ∧
    (∀ t : Fin 33, 0≤whiteHeight (col 6) t.val ∧ whiteHeight (col 6) t.val≤2) ∧
    whiteHeight (col 5) 32=7 ∧ whiteHeight (col 4) 32=3 := by decide +kernel

theorem newest_span_two : SpanTwo (col 6) := by
  apply span_two_of_closed_period (col 6) 32 (by decide) (by decide) (periodic 6)
    height_certificate.1
  refine ⟨0,?_⟩
  intro t ht
  have h := height_certificate.2.1 ⟨t,by omega⟩
  exact h

theorem newest_not_eight : ¬ HeightOneLogic.Periodic (col 6) 8 := by
  intro h
  have hc : col 6 (1+8)≠col 6 1 := by decide +kernel
  exact hc (h 1)

theorem parent_events :
    (col 5 0=false ∧ col 5 1=false) ∧
    (col 5 4=true ∧ col 5 5=true) ∧
    (col 4 0=false ∧ col 4 1=false) ∧
    (col 4 7=true ∧ col 4 8=true) := by decide +kernel

theorem neither_parent_safe_or_coSafe :
    ¬ No00 (col 5) ∧ ¬ No11 (col 5) ∧ ¬ No00 (col 4) ∧ ¬ No11 (col 4) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h;exact h 0 parent_events.1
  · intro h;exact h 4 parent_events.2.1
  · intro h;exact h 0 parent_events.2.2.1
  · intro h;exact h 7 parent_events.2.2.2

theorem neither_parent_height_two : ¬ SpanTwo (col 5) ∧ ¬ SpanTwo (col 4) := by
  constructor
  · rintro ⟨lo,h⟩
    have h0 := h 0;have h32 := h 32
    rw [height_certificate.2.2.1] at h32
    change lo≤0 ∧ 0≤lo+2 at h0
    omega
  · rintro ⟨lo,h⟩
    have h0 := h 0;have h32 := h 32
    rw [height_certificate.2.2.2] at h32
    change lo≤0 ∧ 0≤lo+2 at h0
    omega

end HeightTwoMixedControl
