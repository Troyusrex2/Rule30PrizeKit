import RootEventHeight

/-! A uniform necessary signed-height condition for a Safe child following
a periodic driver and an anti-periodic driver. No finite-white ancestry or
safety converse is assumed or concluded. -/
namespace RootAntiPeriodHeight
open RootEventHeight
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem sign_shift_even (P : Nat) (hp : Even P) (t : Nat) : sign (t+P)=sign t := by
  calc
    sign (t+P)=sign t*sign P := pow_add _ _ _
    _ = sign t := by rw [sign_even P hp,mul_one]

theorem pair_local : ∀ b c : Bool,
    bit (!b && !c)+bit (!b && c)=bit (!b) := by decide +kernel

theorem paired_zero_identity (b c : Nat → Bool) (P : Nat)
    (hb : ∀ t, b (t+P)=b t) (hc : ∀ t, c (t+P)=!c t) (t : Nat) :
    bit (zeroPair b c t)+bit (zeroPair b c (t+P))=bit (!b t) := by
  simpa only [zeroPair,hb t,hc t,Bool.not_not] using pair_local (b t) (c t)

/-- Exact signed projection, including the prefix offset H_Z(P). -/
theorem paired_height_identity (b c : Nat → Bool) (P : Nat) (hp : Even P)
    (hb : ∀ t, b (t+P)=b t) (hc : ∀ t, c (t+P)=!c t) (T : Nat) :
    height (fun t => !b t) T =
      height (zeroPair b c) T + height (zeroPair b c) (T+P)-height (zeroPair b c) P := by
  induction T with
  | zero => simp [height_zero]
  | succ T ih =>
    calc
      height (fun t => !b t) (T+1) = height (fun t => !b t) T + sign T*bit (!b T) :=
        height_succ _ _
      _ = (height (zeroPair b c) T + height (zeroPair b c) (T+P)-height (zeroPair b c) P) +
          sign T*(bit (zeroPair b c T)+bit (zeroPair b c (T+P))) := by
        rw [ih,paired_zero_identity b c P hb hc T]
      _ = height (zeroPair b c) (T+1) + height (zeroPair b c) (T+1+P)-height (zeroPair b c) P := by
        rw [show T+1+P=(T+P)+1 by omega,height_succ,height_succ,sign_shift_even P hp T]
        ring

theorem safe_zero_height_difference (b c d : Nat → Bool)
    (hd : Recurrence b c d) (hs : Safe d) (S T : Nat) :
    -1 ≤ height (zeroPair b c) T-height (zeroPair b c) S ∧
      height (zeroPair b c) T-height (zeroPair b c) S ≤ 1 := by
  have hS := safe_marked_height_range b c d hd hs S
  have hT := safe_marked_height_range b c d hd hs T
  rcases q_cases d 0 with hq|hq <;> rcases hS with hS|hS <;> rcases hT with hT|hT <;> omega

/-- Every signed interval imbalance is at most two, in both directions. -/
theorem safe_complement_height_difference (b c d : Nat → Bool) (P : Nat) (hp : Even P)
    (hb : ∀ t, b (t+P)=b t) (hc : ∀ t, c (t+P)=!c t)
    (hd : Recurrence b c d) (hs : Safe d) (S T : Nat) :
    -2 ≤ height (fun t => !b t) T-height (fun t => !b t) S ∧
      height (fun t => !b t) T-height (fun t => !b t) S ≤ 2 := by
  have h0 := safe_zero_height_difference b c d hd hs S T
  have h1 := safe_zero_height_difference b c d hd hs (S+P) (T+P)
  rw [paired_height_identity b c P hp hb hc T,paired_height_identity b c P hp hb hc S]
  omega

theorem height_period_add (A : Nat → Bool) (P : Nat) (hp : Even P)
    (hA : ∀ t, A (t+P)=A t) (T : Nat) : height A (T+P)=height A T+height A P := by
  induction T with
  | zero => simp [height_zero]
  | succ T ih =>
    rw [show T+1+P=(T+P)+1 by omega,height_succ,ih,height_succ,sign_shift_even P hp T,hA T]
    ring

theorem height_three_periods (A : Nat → Bool) (P : Nat) (hp : Even P)
    (hA : ∀ t, A (t+P)=A t) : height A (3*P)=3*height A P := by
  have htwo := height_period_add A P hp hA P
  have hthree := height_period_add A P hp hA (P+P)
  rw [htwo] at hthree
  rw [show 3*P=(P+P)+P by omega,hthree]
  ring

/-- Bounded integer heights force zero period drift. No driver counts or
unmarked safety converse are used. -/
theorem safe_complement_zero_drift (b c d : Nat → Bool) (P : Nat) (hp : Even P)
    (hb : ∀ t, b (t+P)=b t) (hc : ∀ t, c (t+P)=!c t)
    (hd : Recurrence b c d) (hs : Safe d) : height (fun t => !b t) P=0 := by
  have hcomp : ∀ t, (!b (t+P))=(!b t) := fun t => congrArg Bool.not (hb t)
  have hthree := height_three_periods (fun t => !b t) P hp hcomp
  have hbound := safe_complement_height_difference b c d P hp hb hc hd hs 0 (3*P)
  rw [height_zero,sub_zero,hthree] at hbound
  omega

/-- A2: positive even period, arbitrary periodic/anti-periodic drivers,
and exact all-time Safe child imply zero drift and amplitude at most two. -/
theorem anti_period_safe_necessary (b c d : Nat → Bool) (P : Nat) (_hpos : 0<P) (hp : Even P)
    (hb : ∀ t, b (t+P)=b t) (hc : ∀ t, c (t+P)=!c t)
    (hd : Recurrence b c d) (hs : Safe d) :
    height (fun t => !b t) P=0 ∧ ∀ S T : Nat,
      -2 ≤ height (fun t => !b t) T-height (fun t => !b t) S ∧
        height (fun t => !b t) T-height (fun t => !b t) S ≤ 2 :=
  ⟨safe_complement_zero_drift b c d P hp hb hc hd hs,
    safe_complement_height_difference b c d P hp hb hc hd hs⟩

theorem not_safe_of_height_obstruction (b c d : Nat → Bool) (P : Nat) (hpos : 0<P) (hp : Even P)
    (hb : ∀ t, b (t+P)=b t) (hc : ∀ t, c (t+P)=!c t)
    (hd : Recurrence b c d)
    (hbad : height (fun t => !b t) P≠0 ∨ ∃ S T : Nat,
      2 < height (fun t => !b t) T-height (fun t => !b t) S) : ¬Safe d := by
  intro hs
  obtain ⟨hz,hbound⟩ := anti_period_safe_necessary b c d P hpos hp hb hc hd hs
  rcases hbad with hbad|⟨S,T,hbad⟩
  · exact hbad hz
  · have hbnd := (hbound S T).2
    omega

end RootAntiPeriodHeight
