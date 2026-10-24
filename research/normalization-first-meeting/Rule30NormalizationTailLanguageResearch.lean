import Rule30NormalizationCommonCutResearch

/-! The tail automaton accepts exactly 0* (1 | 11) (01)*, reading the
integer row from low bits to high bits. No infinite-trace theorem is claimed. -/

namespace Rule30NormalizationMachineResearch

def ZeroWord (xs : List Bool) : Prop := ∀ b, b ∈ xs → b = false

inductive StripeWord : List Bool → Prop
  | single (zs : List Bool) (h : ZeroWord zs) : StripeWord (zs ++ [true])
  | double (zs : List Bool) (h : ZeroWord zs) : StripeWord (zs ++ [true,true])
  | extend {xs : List Bool} (h : StripeWord xs) : StripeWord (xs ++ [false,true])

def TailInvariant (xs : List Bool) (s : Nat) : Prop :=
  match s with
  | 0 => ZeroWord xs
  | 1 => ∃ zs, ZeroWord zs ∧ xs = zs ++ [true]
  | 2 => ∃ ys, StripeWord ys ∧ xs = ys ++ [false]
  | 3 => StripeWord xs
  | _ => True

theorem zeroWord_append_false {xs : List Bool} (h : ZeroWord xs) :
    ZeroWord (xs ++ [false]) := by
  intro b hb
  simp only [List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | hb
  · exact h b hb
  · exact hb

theorem tailInvariant_step (xs : List Bool) (s : Nat) (b : Bool)
    (h : TailInvariant xs s) : TailInvariant (xs ++ [b]) (tailNext s b) := by
  rcases s with _ | s
  · cases b
    · exact zeroWord_append_false h
    · exact ⟨xs,h,rfl⟩
  · rcases s with _ | s
    · obtain ⟨zs,hz,rfl⟩ := h
      cases b
      · exact ⟨zs ++ [true],StripeWord.single zs hz,rfl⟩
      · simpa [TailInvariant, tailNext, List.append_assoc] using
          StripeWord.double zs hz
    · rcases s with _ | s
      · obtain ⟨ys,hy,rfl⟩ := h
        cases b
        · trivial
        · simpa [TailInvariant, tailNext, List.append_assoc] using
            StripeWord.extend hy
      · rcases s with _ | s
        · cases b
          · exact ⟨xs,h,rfl⟩
          · trivial
        · cases b <;> trivial

def tailFold (s : Nat) (xs : List Bool) : Nat := xs.foldl tailNext s

theorem tailFold_append (s : Nat) (xs ys : List Bool) :
    tailFold s (xs ++ ys) = tailFold (tailFold s xs) ys := List.foldl_append

theorem tailInvariant_fold (xs ys : List Bool) (s : Nat) (h : TailInvariant xs s) :
    TailInvariant (xs ++ ys) (tailFold s ys) := by
  induction ys generalizing xs s with
  | nil => simpa only [List.append_nil,tailFold,List.foldl_nil] using h
  | cons b ys ih =>
      have hh := ih (xs ++ [b]) (tailNext s b) (tailInvariant_step xs s b h)
      simpa only [List.append_assoc, List.cons_append, List.nil_append,
        tailFold, List.foldl_cons] using hh

theorem tailFold_zero {xs : List Bool} (h : ZeroWord xs) : tailFold 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      have hb := h b (by simp)
      have hx : ZeroWord xs := fun x hx => h x (by simp [hx])
      simpa [tailFold, hb, tailNext] using ih hx

theorem stripeWord_accept {xs : List Bool} (h : StripeWord xs) :
    tailFold 0 xs = 1 ∨ tailFold 0 xs = 3 := by
  induction h with
  | single zs hz =>
      left
      rw [tailFold_append, tailFold_zero hz]
      rfl
  | double zs hz =>
      right
      rw [tailFold_append, tailFold_zero hz]
      rfl
  | extend h ih =>
      right
      rw [tailFold_append]
      rcases ih with hi | hi <;> rw [hi] <;> rfl

theorem tailFold_accept_iff (xs : List Bool) :
    tailFold 0 xs = 1 ∨ tailFold 0 xs = 3 ↔ StripeWord xs := by
  constructor
  · intro h
    have hz : TailInvariant [] 0 := by intro b hb; simp at hb
    have hi := tailInvariant_fold [] xs 0 hz
    simp only [List.nil_append] at hi
    rcases h with h | h
    · rw [h] at hi
      obtain ⟨zs,hz,rfl⟩ := hi
      exact StripeWord.single zs hz
    · simpa only [h, TailInvariant] using hi
  · exact stripeWord_accept

def rowBits (a n : Nat) : List Bool := (List.range n).map a.testBit

theorem rowBits_succ (a n : Nat) : rowBits a (n+1) = rowBits a n ++ [a.testBit n] := by
  simp only [rowBits, List.range_succ, List.map_append, List.map_singleton]

theorem tailRun_eq_fold (a n : Nat) : tailRun a n = tailFold 0 (rowBits a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [rowBits_succ, tailFold_append, ← ih]
      rfl

theorem tailRun_accept_iff (a n : Nat) :
    tailRun a n = 1 ∨ tailRun a n = 3 ↔ StripeWord (rowBits a n) := by
  rw [tailRun_eq_fold]
  exact tailFold_accept_iff _

def StripeRelated (a b c : Nat) : Prop := a = b ∨ ∃ j, j ≤ c ∧
  StripeWord (rowBits a (j+1)) ∧ StripeWord (rowBits b (j+1)) ∧
  a.testBit j = true ∧ b.testBit j = true ∧
  a.testBit (j+1) = false ∧ b.testBit (j+1) = false ∧
  ∀ i, j+1 < i → a.testBit i = b.testBit i

theorem rowRelated_iff_stripeRelated (a b c : Nat) :
    RowRelated a b c ↔ StripeRelated a b c := by
  unfold RowRelated StripeRelated EligibleCut
  simp only [tailRun_accept_iff]
  constructor
  · rintro (he | ⟨j,⟨hc,ha,hb,hsa,hsb⟩,hza,hzb,hs⟩)
    · exact Or.inl he
    · exact Or.inr ⟨j,hc,hsa,hsb,ha,hb,hza,hzb,hs⟩
  · rintro (he | ⟨j,hc,hsa,hsb,ha,hb,hza,hzb,hs⟩)
    · exact Or.inl he
    · exact Or.inr ⟨j,⟨hc,ha,hb,hsa,hsb⟩,hza,hzb,hs⟩

/-- A pair with equal first two center observations cannot first become
stripe-related on the second step. This quantifies over all finite integer
rows and all center indices, with no bound on their sizes. -/
theorem two_step_stripe_related (a b c : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (h2 : StripeRelated (Phi (Phi a)) (Phi (Phi b)) (c+2)) :
    StripeRelated a b c ∨ StripeRelated (Phi a) (Phi b) (c+1) := by
  have h := two_step_common_cut a b c h0 h1
    ((rowRelated_iff_stripeRelated _ _ _).mpr h2)
  rcases h with h | h
  · exact Or.inl ((rowRelated_iff_stripeRelated _ _ _).mp h)
  · exact Or.inr ((rowRelated_iff_stripeRelated _ _ _).mp h)

end Rule30NormalizationMachineResearch
