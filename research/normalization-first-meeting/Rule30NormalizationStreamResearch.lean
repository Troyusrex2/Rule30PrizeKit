import Rule30NormalizationPackingResearch
import Rule30NormalizationMachineSoundnessResearch

/-! Typed stream semantics for the checked packed machine. Actual-row
and stripe-language semantics are proved in companion modules; numerical
normalization and infinite-trace completeness remain open. -/

namespace Rule30NormalizationMachineResearch

def nextCode (old : Nat) (marker : Bool) : Nat :=
  if marker then 1 else if old == 0 then 0 else min 4 (old+1)

theorem nextCode_le (old : Nat) (marker : Bool) : nextCode old marker ≤ 4 := by
  unfold nextCode
  split
  · decide
  · split
    · decide
    · exact Nat.min_le_left _ _

def View.advance (v : View) (a b marker : Bool) : Option View :=
  if marker && v.code != 0 then none else
  let code := nextCode v.code marker
  let a1 := first v.ha a
  let b1 := first v.hb b
  if (code == 1 && a != b) || (code == 2 && a1 != b1) then none else
  some ⟨relStep v.e0 a b (code == 0 || code ≤ 1),
    relStep v.e1 a1 b1 (code == 0 || code ≤ 2),
    relStep v.e2 (second v.ha a) (second v.hb b) (code == 0 || code ≤ 3),
    (2 * v.ha + a.toNat) % 16, (2 * v.hb + b.toNat) % 16, code⟩

theorem View.encode_advance (v : View) (hv : v.Valid) (a b marker : Bool) :
    step v.encode (symbol a b marker) = (v.advance a b marker).map View.encode := by
  obtain ⟨h0,h1,h2,ha,hb,hc⟩ := v.decode_encode hv
  obtain ⟨s0,s1,s2⟩ := symbol_bits a b marker
  have hcode : (if marker then 1 else if v.code == 0 then 0 else min 4 (v.code+1)) =
      nextCode v.code marker := rfl
  simp only [step, View.advance, h0,h1,h2,ha,hb,hc,s0,s1,s2,hcode]
  split
  · rfl
  · split <;> rfl

theorem View.advance_valid {v w : View} {a b marker : Bool}
    (h : v.advance a b marker = some w) : w.Valid := by
  unfold View.advance at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · simp at h
    · have he := Option.some.inj h
      subst w
      exact ⟨relStep_lt _ _ _ _, relStep_lt _ _ _ _, relStep_lt _ _ _ _,
        Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), nextCode_le _ _⟩

structure Letter where
  a : Bool
  b : Bool
  marker : Bool

def Letter.val (x : Letter) : Nat := symbol x.a x.b x.marker

def View.run (v : View) : List Letter → Option View
  | [] => some v
  | x :: xs => (v.advance x.a x.b x.marker).bind (fun w => w.run xs)

theorem View.run_encode (v : View) (hv : v.Valid) (xs : List Letter) :
    Rule30NormalizationMachineResearch.run v.encode (xs.map Letter.val) = (v.run xs).map View.encode := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, Rule30NormalizationMachineResearch.run, View.run, Letter.val]
      rw [v.encode_advance hv]
      cases h : v.advance x.a x.b x.marker with
      | none => simp only [Option.map_none, Option.bind_none]
      | some w =>
          simp only [Option.map_some, Option.bind_some]
          exact ih w (View.advance_valid h)

def initialView : View := ⟨4,4,4,0,0,0⟩

theorem initialView_valid : initialView.Valid := by unfold View.Valid initialView; decide
theorem initialView_encode : initialView.encode = initial := by decide

theorem safe_after_input (xs : List Letter) {v : View} (h : initialView.run xs = some v) :
    endGood v.encode = true := by
  have hr : Rule30NormalizationMachineResearch.run initial (xs.map Letter.val) = some v.encode := by
    rw [← initialView_encode, initialView.run_encode initialView_valid, h]
    rfl
  apply all_input_lengths_safe (xs.map Letter.val) _ hr
  intro u hu
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hu
  exact symbol_lt x.a x.b x.marker

end Rule30NormalizationMachineResearch
