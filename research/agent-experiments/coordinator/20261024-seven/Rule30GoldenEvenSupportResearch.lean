import Rule30GoldenDFAResearch

/-! A prescribed-even-coordinate decoder with a golden free-bit guard.
Odd initial spatial cells are unrestricted. The checker-soundness theorem
is conditional on its finite calculation; no claim for all widths is made. -/

namespace Rule30GoldenEvenSupportResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundary (alt recon)
open Rule30ZeroBoundaryLanes (AD scanN mapX level scanN_lin pat pats_getD pat_spec
  pack pack_lt testBit_pack yFree)
open Rule30GoldenDFAResearch (Golden Flags)

structure State where
  R : List Nat
  Rm : List Nat
  flags : Flags

def start (ALL : Nat) : State := ⟨[],[],Rule30GoldenDFAResearch.initial ALL⟩

noncomputable def step (ALL : Nat) (E : Nat → Nat) (d : Nat) (st : State) : State :=
  let a := scanN ALL st.R (0 :: st.Rm)
  let R1 := ALL :: a.1
  let b := scanN 0 R1 (0 :: st.R)
  let Y := E d ^^^ b.2
  ⟨Y :: mapX Y b.1, R1, Rule30GoldenDFAResearch.advance ALL Y st.flags⟩

noncomputable def run (ALL : Nat) (E : Nat → Nat) : Nat → Nat → State → State :=
  Nat.rec (motive := fun _ => Nat → State → State) (fun _ st => st)
    (fun _ ih d st => Bool.rec
      (ih (d+1) (step ALL E d st)) st (Rule30GoldenDFAResearch.empty st.flags))

theorem run_zero (ALL : Nat) (E : Nat → Nat) (d : Nat) (st : State) : run ALL E 0 d st = st := rfl

theorem run_succ (ALL : Nat) (E : Nat → Nat) (fuel d : Nat) (st : State) :
    run ALL E (fuel+1) d st = Bool.rec
      (run ALL E fuel (d+1) (step ALL E d st)) st (Rule30GoldenDFAResearch.empty st.flags) := rfl

def Matches (s : Nat → Bool) (p d : Nat) (st : State) : Prop :=
  st.R.map (fun a => a.testBit p) = AD (alt s) (2*d) 0 (2*d) ∧
  st.Rm.map (fun a => a.testBit p) = AD (alt s) (2*d-1) 0 (2*d-1) ∧
  (st.flags.at (Rule30GoldenDFAResearch.run s d)).testBit p = true

def code (s : Nat → Bool) (d : Nat) : Bool := recon (alt s) (2*d+2) 0

theorem alt_even (s : Nat → Bool) (d : Nat) : alt s (2*d) = true := by
  unfold alt
  rw [ite_eq_left (by omega)]

theorem alt_odd (s : Nat → Bool) (d : Nat) : alt s (2*d+1) = s d := by
  unfold alt
  rw [ite_eq_right (by omega), show (2*d+1)/2 = d by omega]

theorem start_matches {ALL p : Nat} (hALL : ALL.testBit p = true) (s : Nat → Bool) :
    Matches s p 0 (start ALL) := ⟨rfl,rfl,hALL⟩

theorem step_matches {ALL p d : Nat} {E : Nat → Nat} {s : Nat → Bool} {st : State}
    (hALL : ALL.testBit p = true) (hgold : Golden s) (hinput : (E d).testBit p = code s d)
    (hm : Matches s p d st) : Matches s p (d+1) (step ALL E d st) := by
  obtain ⟨hR,hRm,hflags⟩ := hm
  let R1 := ALL :: (scanN ALL st.R (0 :: st.Rm)).1
  let b := scanN 0 R1 (0 :: st.R)
  let Y := E d ^^^ b.2
  have hY1 : ALL.testBit p = alt s (2*d) := by rw [hALL,alt_even]
  have h1 := level (alt s) p (2*d) st.R st.Rm ALL hR hRm hY1
  have hR1 : R1.map (fun a => a.testBit p) = AD (alt s) (2*d+1) 0 (2*d+1) := h1.1
  have hRold : st.R.map (fun a => a.testBit p) = AD (alt s) (2*d+1-1) 0 (2*d+1-1) := by
    simpa only [show 2*d+1-1 = 2*d by omega] using hR
  let Y' : Nat := if s d then 2^p else 0
  have hy' : Y'.testBit p = s d := by
    cases hs : s d <;> simp [Y',hs]
  have hy'alt : Y'.testBit p = alt s (2*d+1) := by rw [alt_odd]; exact hy'
  have hp := (level (alt s) p (2*d+1) R1 st.R Y' hR1 hRold hy'alt).2
  have hp' : xor (s d) (b.2.testBit p) = code s d := by
    rw [scanN_lin R1 (0 :: st.R) Y',Nat.testBit_xor,hy'] at hp
    simpa only [code,show 2*d+1+1 = 2*d+2 by omega] using hp
  have hy : Y.testBit p = s d := by
    change (E d ^^^ b.2).testBit p = s d
    rw [Nat.testBit_xor,hinput]
    cases hs : s d <;> cases hb : b.2.testBit p <;> cases hc : code s d <;> simp_all
  have hyalt : Y.testBit p = alt s (2*d+1) := by rw [alt_odd]; exact hy
  have h2 := (level (alt s) p (2*d+1) R1 st.R Y hR1 hRold hyalt).1
  rw [scanN_lin R1 (0 :: st.R) Y] at h2
  refine ⟨?_,?_,?_⟩
  · change (Y :: mapX Y b.1).map (fun a => a.testBit p) = AD (alt s) (2*(d+1)) 0 (2*(d+1))
    simpa only [show 2*(d+1) = 2*d+1+1 by omega] using h2
  · change R1.map (fun a => a.testBit p) = AD (alt s) (2*(d+1)-1) 0 (2*(d+1)-1)
    simpa only [show 2*(d+1)-1 = 2*d+1 by omega] using hR1
  · change ((Rule30GoldenDFAResearch.advance ALL Y st.flags).at
      (Rule30GoldenDFAResearch.run s (d+1))).testBit p = true
    rw [Rule30GoldenDFAResearch.run]
    exact Rule30GoldenDFAResearch.advance_contains hALL hy (Rule30GoldenDFAResearch.run_lt hgold d)
      hflags (by simpa only [Rule30GoldenDFAResearch.run] using Rule30GoldenDFAResearch.run_lt hgold (d+1))

theorem run_matches {ALL p : Nat} {E : Nat → Nat} {s : Nat → Bool}
    (hALL : ALL.testBit p = true) (hgold : Golden s)
    (hinput : ∀ d, (E d).testBit p = code s d) (fuel : Nat) :
    ∀ d st, Matches s p d st → Matches s p (d+fuel) (run ALL E fuel d st) := by
  induction fuel with
  | zero => intro d st hm; simpa only [run_zero,Nat.add_zero] using hm
  | succ fuel ih =>
    intro d st hm
    have hn := Rule30GoldenDFAResearch.not_empty_of_contains (Rule30GoldenDFAResearch.run_lt hgold d) hm.2.2
    have he : Rule30GoldenDFAResearch.empty st.flags = false := by
      cases hb : Rule30GoldenDFAResearch.empty st.flags
      · rfl
      · exact False.elim (hn hb)
    rw [run_succ,he]
    have hstep := step_matches hALL hgold (hinput d) hm
    have hi := ih (d+1) (step ALL E d st) hstep
    simpa only [show d+1+fuel = d+(fuel+1) by omega] using hi

theorem run_not_empty {ALL p : Nat} {E : Nat → Nat} {s : Nat → Bool}
    (hALL : ALL.testBit p = true) (hgold : Golden s)
    (hinput : ∀ d, (E d).testBit p = code s d) (fuel : Nat) :
    Rule30GoldenDFAResearch.empty (run ALL E fuel 0 (start ALL)).flags ≠ true := by
  have h := run_matches hALL hgold hinput fuel 0 (start ALL) (start_matches hALL s)
  exact Rule30GoldenDFAResearch.not_empty_of_contains (Rule30GoldenDFAResearch.run_lt hgold (0+fuel)) h.2.2

def allMask (n : Nat) : Nat := 2^(2^n)-1

noncomputable def check (n c K : Nat) : Bool :=
  let ALL := allMask n
  let pats := (List.range n).map (pat n)
  Rule30GoldenDFAResearch.empty (run ALL (yFree n c ALL pats) K 0 (start ALL)).flags

def NoGoldenEvenWidth (M : Nat) : Prop :=
  ∀ s : Nat → Bool, (∀ d, M ≤ d → code s d = false) → ¬ Golden s

theorem no_golden_even_width_of_checks (M n K : Nat) (hn : n ≤ M)
    (hchecks : ∀ c, c < 2^(M-n) → check n c K = true) : NoGoldenEvenWidth M := by
  intro s hwidth hgold
  let p := pack (code s) n
  let c := pack (fun i => code s (n+i)) (M-n)
  let ALL := allMask n
  let pats := (List.range n).map (pat n)
  have hp : p < 2^n := pack_lt (code s) n
  have hc : c < 2^(M-n) := pack_lt (fun i => code s (n+i)) (M-n)
  have hALL : ALL.testBit p = true := by
    dsimp [ALL,allMask]
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hp
  have hinput : ∀ d, (yFree n c ALL pats d).testBit p = code s d := by
    intro d
    by_cases hd : d < n
    · unfold yFree
      rw [ite_eq_left hd]
      have hpat : pats.getD d 0 = pat n d := pats_getD n d hd
      rw [hpat,pat_spec n d p hd hp]
      dsimp [p]
      rw [testBit_pack]
      simp only [decide_eq_true hd,Bool.true_and]
    · have hbit : c.testBit (d-n) = code s d := by
        dsimp [c]
        rw [testBit_pack,show n+(d-n) = d by omega]
        by_cases hM : d < M
        · simp only [decide_eq_true (show d-n < M-n by omega),Bool.true_and]
        · rw [hwidth d (by omega)]
          simp
      unfold yFree
      rw [ite_eq_right hd]
      cases hb : c.testBit (d-n) <;> simp_all
  have hbad := run_not_empty hALL hgold hinput K
  exact hbad (hchecks c hc)

end Rule30GoldenEvenSupportResearch
