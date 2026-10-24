import Rule30ExternalSkelPairAudit

/-! Constructive inversion of the even-depth coordinates in the exact
reconstruction of G.P.J.W. Quint and Gemini. The finite-support statement
below is a reformulation of OPEN Q01, not a proof of Q01 or Problem 1. -/

namespace Rule30EvenDecodeResearch

open Ruliology.CellularAutomata Rule30Submission

def evenCode (s : Nat → Bool) (d : Nat) : Bool :=
  (skelPair s (2*d+2) 0).1

/-- Causal inversion: compute a new free bit from the preceding free bits
and the requested even spatial cell. All later free bits are set to zero
in this temporary prefix; locality makes their choice irrelevant. -/
def decode (u : Nat → Bool) (d : Nat) : Bool :=
  xor (u d) (skelPair (fun i => if _h : i < d then decode u i else false) (2*d+2) 0).1
termination_by d

theorem evenCode_decode (u : Nat → Bool) : evenCode (decode u) = u := by
  funext d
  let p : Nat → Bool := fun i => if i < d then decode u i else false
  have hp := (skelPair_locality_and_pivot d).2.2.1 (decode u) p 0
    (fun i _ hi => by simp only [Nat.zero_add] at hi; simp [p, hi])
  have hpd : p d = false := by simp [p]
  simp only [Nat.zero_add, hpd, Bool.xor_false] at hp
  have hd : decode u d = xor (u d) (skelPair p (2*d+2) 0).1 := by
    rw [decode]
    have hfun : (fun i => if _h : i < d then decode u i else false) = p := by
      funext i
      by_cases hi : i < d <;> simp [p, hi]
    rw [hfun]
  unfold evenCode
  rw [hp, hd]
  cases u d <;> cases (skelPair p (2*d+2) 0).1 <;> rfl

theorem evenCode_injective : Function.Injective evenCode := by
  intro s t h
  funext d
  exact free_bits_unique_of_even_depths s t (d+1)
    (fun i _ => congrFun h i) d (by omega)

theorem decode_evenCode (s : Nat → Bool) : decode (evenCode s) = s := by
  apply evenCode_injective
  exact evenCode_decode (evenCode s)

theorem evenCode_bijective : Function.Bijective evenCode :=
  ⟨evenCode_injective, fun u => ⟨decode u, evenCode_decode u⟩⟩

theorem decode_locality {u v : Nat → Bool} (d : Nat)
    (h : ∀ i, i < d → u i = v i) : ∀ i, i < d → decode u i = decode v i := by
  apply free_bits_unique_of_even_depths (decode u) (decode v) d
  intro i hi
  change evenCode (decode u) i = evenCode (decode v) i
  rw [evenCode_decode, evenCode_decode]
  exact h i hi

/-- The initial odd spatial cells forced by the prescribed even cells. -/
def oddCode (u : Nat → Bool) (d : Nat) : Bool :=
  (skelPair (decode u) (2*d+1) 0).1

theorem oddCode_locality {u v : Nat → Bool} (d : Nat)
    (h : ∀ i, i < d → u i = v i) : oddCode u d = oddCode v d := by
  apply odd_depth_determined_by_even_depths
  intro i hi
  change evenCode (decode u) i = evenCode (decode v) i
  rw [evenCode_decode, evenCode_decode]
  exact h i hi

def FiniteBits (u : Nat → Bool) : Prop := ∃ N, ∀ d, N ≤ d → u d = false

theorem finite_tail_has_last {f : Nat → Bool} (h1 : f 1 = true)
    (hf : FiniteBits f) : ∃ m, 0 < m ∧ f m = true ∧ ∀ n, m < n → f n = false := by
  obtain ⟨N, hN⟩ := hf
  induction N with
  | zero =>
      have := hN 1 (by omega)
      rw [h1] at this
      cases this
  | succ N ih =>
      by_cases hb : f N = true
      · have hn : 0 < N := by
          by_contra hn
          have hzero : N = 0 := by omega
          subst N
          have := hN 1 (by omega)
          rw [h1] at this
          cases this
        exact ⟨N, hn, hb, fun n hn => hN n (by omega)⟩
      · apply ih
        intro n hn
        by_cases he : n = N
        · subst n
          cases h : f N
          · rfl
          · exact False.elim (hb h)
        · exact hN n (by omega)

theorem finite_even_odd_iff (s : Nat → Bool) :
    FiniteBits (fun m => (skelPair s m 0).1) ↔
      FiniteBits (evenCode s) ∧ FiniteBits (oddCode (evenCode s)) := by
  constructor
  · rintro ⟨N, hN⟩
    constructor
    · exact ⟨N, fun d hd => hN (2*d+2) (by omega)⟩
    · refine ⟨N, fun d hd => ?_⟩
      simpa only [oddCode, decode_evenCode] using hN (2*d+1) (by omega)
  · rintro ⟨⟨N, hN⟩, ⟨M, hM⟩⟩
    refine ⟨2*(N+M+1), fun n hn => ?_⟩
    by_cases he : n % 2 = 0
    · have hn' : n = 2*((n-2)/2)+2 := by omega
      rw [hn']
      exact hN ((n-2)/2) (by omega)
    · have hn' : n = 2*((n-1)/2)+1 := by omega
      rw [hn']
      have := hM ((n-1)/2) (by omega)
      simpa only [oddCode, decode_evenCode] using this

/-- Q01 is exactly the remaining infinite-tail assertion for finite prescribed
even coordinates. The assertion on the right is OPEN. -/
theorem Q01_iff_finite_even_infinite_odd :
    Rule30PeriodTwo.Q01 ↔ ∀ u, FiniteBits u → ¬ FiniteBits (oddCode u) := by
  constructor
  · intro hQ u hu ho
    have hf : FiniteBits (fun m => (skelPair (decode u) m 0).1) := by
      apply (finite_even_odd_iff (decode u)).mpr
      simpa only [evenCode_decode] using And.intro hu ho
    obtain ⟨m, hm, hb, hw⟩ := finite_tail_has_last (by rfl) hf
    exact (Q01_iff_no_skelPair_support.mp hQ) ⟨decode u, m, hm, hb, hw⟩
  · intro h
    apply Q01_iff_no_skelPair_support.mpr
    rintro ⟨s, m, hm, hb, hw⟩
    have hf : FiniteBits (fun n => (skelPair s n 0).1) :=
      ⟨m+1, fun n hn => hw n (by omega)⟩
    obtain ⟨he, ho⟩ := (finite_even_odd_iff s).mp hf
    exact h (evenCode s) he ho

end Rule30EvenDecodeResearch
