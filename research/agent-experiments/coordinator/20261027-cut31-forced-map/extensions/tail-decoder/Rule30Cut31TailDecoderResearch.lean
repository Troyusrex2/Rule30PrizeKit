module

public import Rule30Cut31ForcedMapResearch

/-!
# Recovering the original gate tail from the complete cut-31 observation

These local decoders recover actual short-gap markers and the actual original
gate after seven samples. They do not assert a second physical reset, finite
support preservation by decoding, or a class closed under further cuts.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Cut31TailDecoderResearch

open Rule30Cut31ForcedMapResearch Rule30EmptyGateLanguageResearch

def markerRead (l : Nat → Bool) (r : Nat) : Bool := l (2*r) && l (2*r+2)

theorem marker_certificate : allowed17.all (fun w => decide
    ((lEven w.testBit 0 && lEven w.testBit 1) = pulse w.testBit 7)) = true := by
  decide

theorem marker_polynomial (r : Nat) :
    (lEven refinedGate r && lEven refinedGate (r+1)) = pulse refinedGate (r+7) := by
  have h := of_decide_eq_true (List.all_eq_true.mp marker_certificate
    (word refinedGate r 17) (actual_seventeen r))
  simpa [lEven,pulse,word,pack_bit,Nat.add_assoc] using h

/-- Two adjacent even-time forcing observations recover the actual old short-gap marker. -/
theorem actual_marker_decoder (r : Nat) :
    markerRead (L refinedGate) r = pulse refinedGate (r+7) := by
  unfold markerRead
  rw [(cut31_actual r).2.2.1, show 2*r+2=2*(r+1) by omega,
    (cut31_actual (r+1)).2.2.1]
  exact marker_polynomial r

def gateRead (b l : Nat → Bool) (r : Nat) : Bool :=
  xor (xor (xor (xor (xor (!b (2*r+12)) (markerRead l r))
    (markerRead l (r+4))) (markerRead l (r+6)))
    (markerRead l (r+7))) (markerRead l (r+11))

theorem xor_recover (g a b c d e : Bool) :
    xor (xor (xor (xor (xor
      (!xor (xor (xor (xor (xor (!g) a) b) c) d) e) a) b) c) d) e = g := by
  cases g <;> cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

/-- The full cut-31 observation recovers the actual original gate from index seven onward. -/
theorem actual_gate_tail_decoder (r : Nat) :
    gateRead (B refinedGate) (L refinedGate) r = refinedGate (r+7) := by
  unfold gateRead
  rw [show 2*r+12=2*(r+6) by omega, (cut31_actual (r+6)).1]
  rw [actual_marker_decoder,actual_marker_decoder,actual_marker_decoder,
    actual_marker_decoder,actual_marker_decoder]
  simp only [bEven,Nat.add_assoc]
  exact xor_recover _ _ _ _ _ _

end Ruliology.CellularAutomata.Rule30Cut31TailDecoderResearch
