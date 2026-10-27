module
public import Rule30CAGateReturnResearch

/-! A gated child inherits a period of the older two observation streams.
No whole older return is assumed. The first-reset argument is the scalar
mechanism of Rule30ForwardResetResearch, specialized here to a reset latch.
The result concerns observations only; no gate inheritance is asserted. -/
@[expose] public section
namespace Rule30GatedObservationResetResearch
open Rule30CommonPastResearch Rule30ReaderCanonicalResearch Rule30CAObserverResearch
open Rule30CAClockDemodulationResearch Rule30CAGateReturnResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def Period (x : Nat → Bool) (P : Nat) : Prop := ∀ t, x (t+P)=x t

theorem period_mul {x : Nat → Bool} {P : Nat} (hp : Period x P) (k t : Nat) :
    x (t+k*P)=x t := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul,← Nat.add_assoc,hp,ih]

theorem latch_eventual {x f c : Nat → Bool} {P : Nat}
    (hx : ∀ t, x (t+1)=if c t then !(f t) else x t)
    (hf : Period f P) (hc : Period c P) (hP : 0<P) :
    ∀ t, P≤t → x (t+P)=x t := by
  classical
  by_cases hex : ∃ A, c A=true
  · obtain ⟨A,hA⟩ := hex
    let R := A%P
    have hR : R<P := Nat.mod_lt A hP
    have hb : c R=true := by
      have hh := period_mul hc (A/P) R
      have he : R+(A/P)*P=A := by
        have hd := Nat.mod_add_div A P
        rw [Nat.mul_comm P (A/P)] at hd
        exact hd
      rw [he,hA] at hh
      exact hh.symm
    have start : x (R+1+P)=x (R+1) := by
      rw [show R+1+P=R+P+1 by omega,hx,hx,hc,hf,hb]
      simp
    have future : ∀ s, x (R+1+s+P)=x (R+1+s) := by
      intro s
      induction s with
      | zero => simpa using start
      | succ s ih =>
          rw [show R+1+(s+1)+P=(R+1+s+P)+1 by omega,
            show R+1+(s+1)=(R+1+s)+1 by omega,hx,hx,hc,hf,ih]
    intro t ht
    simpa only [show R+1+(t-(R+1))=t by omega] using future (t-(R+1))
  · have hz : ∀ t, c t=false := by
      intro t
      cases hh : c t
      · rfl
      · exact (hex ⟨t,hh⟩).elim
    have hconst : ∀ t, x t=x 0 := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => simpa only [hx,hz,Bool.false_eq_true,ite_false] using ih
    intro t _
    exact (hconst _).trans (hconst _).symm

theorem latch_period {x f c : Nat → Bool} {P M : Nat}
    (hx : ∀ t, x (t+1)=if c t then !(f t) else x t)
    (hf : Period f P) (hc : Period c P) (hP : 0<P)
    (hM : 0<M) (hm : Period x M) : Period x P := by
  intro t
  have hl : P≤P*M := by
    have hh := Nat.mul_le_mul_left P (Nat.succ_le_of_lt hM)
    simpa using hh
  have h := latch_eventual hx hf hc hP (t+P*M) (by omega)
  rw [show t+P*M+P=(t+P)+P*M by omega,period_mul hm P (t+P),period_mul hm P t] at h
  exact h

theorem memory_append (p q : Bool) (xs ys : List Bool) :
    memory p q (xs++ys)=memory (memory p q xs).1 (memory p q xs).2 ys := by
  induction xs generalizing p q with
  | nil => rfl
  | cons a xs ih => exact ih a p

theorem snoc_of_nonempty (u : List Bool) (hu : u≠[]) : ∃ v f, u=v++[f] := by
  induction u with
  | nil => exact (hu rfl).elim
  | cons a u ih =>
      cases u with
      | nil => exact ⟨[],a,rfl⟩
      | cons b u =>
          obtain ⟨v,f,h⟩ := ih (by simp)
          exact ⟨a::v,f,by rw [h]; rfl⟩

theorem two_step_last (u : List Bool) (hu : u≠[]) (g : Bool) :
    xor (g || r u) (halfBit u g || s u)=
      ((xor (r u) (s u)) && xor true (xor g (r u))) := by
  obtain ⟨v,f,rfl⟩ := snoc_of_nonempty u hu
  have hr : r (v++[f])=f := last_append_one false v f
  have hs : s (v++[f])=xor f (force false false v) := by
    unfold s A singleStep
    rw [change_append_one]
    exact last_append_one false _ _
  have hforce : force false false (v++[f])=(f || r v) := by
    unfold force
    rw [memory_append]
    simp only [memory,memory_first]
    rfl
  rw [hr,hs]
  unfold halfBit
  rw [hforce]
  unfold force
  rw [memory_first]
  change xor (g || f) (xor g (f || r v) || xor f (r v || (memory false false v).2))=
    ((xor f (xor f (r v || (memory false false v).2))) && xor true (xor g f))
  cases g <;> cases f <;> cases r v <;> cases (memory false false v).2 <;> rfl

theorem gated_latch (u : List Bool) (g h : Bool) (hu : u≠[]) (hg : Gated u g h) (t : Nat) :
    giter u g (t+1)=if xor (outR u t) (outS u t) then !(outR u t) else giter u g t := by
  obtain ⟨b,hb⟩ := titer_append_two u g h hu t
  have hbval : b= !(giter u g t) := by
    have hh := (hg t).1
    unfold outR at hh
    rw [hb] at hh
    simpa only [r,last_append_two] using hh
  have hh := (hg (t+1)).1
  unfold outR at hh
  change r (T (titer (u++[g,h]) t))= !(giter u g (t+1)) at hh
  rw [hb,T_append_two _ _ _ (titer_nonempty hu t)] at hh
  simp only [r,last_append_two] at hh
  change xor (xor b (giter u g t || r (titer u t)))
    (halfBit (titer u t) (giter u g t) || s (titer u t))= !(giter u g (t+1)) at hh
  rw [hbval,xor_three,two_step_last _ (titer_nonempty hu t)] at hh
  change xor (!(giter u g t))
    ((xor (outR u t) (outS u t)) && xor true (xor (giter u g t) (outR u t)))=
    !(giter u g (t+1)) at hh
  cases hg0 : giter u g t <;> cases hg1 : giter u g (t+1) <;>
    cases hf : outR u t <;> cases hs : outS u t <;> simp_all

theorem outR_has_period (xs : List Bool) : ∃ M, 0<M ∧ Period (outR xs) M := by
  let n := (word0 xs).length
  refine ⟨2^n,Nat.two_pow_pos _,?_⟩
  intro t
  have hp := iter_period (word0 xs) (n+1) (by dsimp [n]; omega) (2*t)
  have he : 2*t+2^(n+1)=2*(t+2^n) := by rw [Nat.pow_succ]; omega
  rw [he,(iter_even_odd xs (t+2^n)).1,(iter_even_odd xs t).1] at hp
  have hh := congrArg r hp
  change r (titer xs (t+2^n))=r (titer xs t)
  simpa only [r_word0] using hh

/-- The supplied period belongs only to the older two observations.
The conclusion also concerns only the two observations, not whole return. -/
theorem gated_observation_period (u : List Bool) (g h : Bool) (P : Nat)
    (hu : u≠[]) (hP : 0<P) (hg : Gated u g h)
    (hR : Period (outR u) P) (hS : Period (outS u) P) :
    Period (outR (u++[g,h])) P ∧ Period (outS (u++[g,h])) P := by
  have hc : Period (fun t => xor (outR u t) (outS u t)) P := by
    intro t
    change xor (outR u (t+P)) (outS u (t+P))=xor (outR u t) (outS u t)
    rw [hR t,hS t]
  have hidentify : ∀ t, outR (u++[g]) t=giter u g t := by
    intro t
    unfold outR
    rw [titer_append_one]
    exact last_append_one false _ _
  obtain ⟨M,hM,hm⟩ := outR_has_period (u++[g])
  have hgm : Period (giter u g) M := by
    intro t
    simpa only [hidentify] using hm t
  have hgp := latch_period (gated_latch u g h hu hg) hR hc hP hM hgm
  constructor
  · intro t
    rw [(hg (t+P)).1,(hg t).1,hgp t]
  · intro t
    rw [(hg (t+P)).2,(hg t).2]

end Rule30GatedObservationResetResearch
