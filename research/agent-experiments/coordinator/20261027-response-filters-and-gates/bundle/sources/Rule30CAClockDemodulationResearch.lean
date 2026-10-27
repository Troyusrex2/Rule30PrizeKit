module
public import Ruliology.CellularAutomata.Rule30Prize
public import Rule30AnchoredConstantResearch

/-! Actual finite-tail CA observations detect a penultimate anti-period and
recover the older two observations. A supplied whole older return is essential;
the zero-displacement case asserts no plateau reconstruction. -/
@[expose] public section
namespace Rule30CAClockDemodulationResearch
open Rule30ReaderCanonicalResearch Rule30CAObserverResearch
open Rule30AnchoredConstantResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def outR (xs : List Bool) (t : Nat) := r (titer xs t)
def outS (xs : List Bool) (t : Nat) := s (titer xs t)
def delta (P : Nat) (a : Nat → Bool) (t : Nat) := xor (a (t+P)) (a t)
def demodR (P : Nat) (xs : List Bool) :=
  delta P (fun t => xor (outR xs t) (outS xs t))
def demodS (P : Nat) (xs : List Bool) :=
  delta P (fun t => xor (outS xs t) (outR xs (t+1)))
def birth (P : Nat) (u : List Bool) (g : Bool) :=
  xor (r (titer (u++[g]) P)) g

def memory (p q : Bool) : List Bool → Bool × Bool
  | [] => (p,q)
  | b::bs => memory b p bs
def force (p q : Bool) (xs : List Bool) :=
  (memory p q xs).1 || (memory p q xs).2
def halfBit (xs : List Bool) (g : Bool) := xor g (force false false xs)
def drive (xs : List Bool) := xor (force false false xs) (force true false (A xs))
def giter (u : List Bool) (g : Bool) : Nat → Bool
  | 0 => g
  | t+1 => xor (giter u g t) (drive (titer u t))

theorem xor_three (a b c : Bool) : xor (xor a b) c=xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem xor_twice (a b : Bool) : xor a (xor a b)=b := by
  cases a <;> cases b <;> rfl
theorem xor_same_right (a b c : Bool) : xor (xor a c) (xor b c)=xor a b := by
  cases a <;> cases b <;> cases c <;> rfl
theorem or_difference (a b c : Bool) :
    xor (a || c) (b || c)=(xor a b && !c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem memory_first (p q : Bool) (xs : List Bool) :
    (memory p q xs).1=lastBit p xs := by
  induction xs generalizing p q with
  | nil => rfl
  | cons b bs ih => exact ih b p

theorem change_append (p q : Bool) (xs ys : List Bool) :
    singleChange p q (xs++ys)=singleChange p q xs ++
      singleChange (memory p q xs).1 (memory p q xs).2 ys := by
  induction xs generalizing p q with
  | nil => rfl
  | cons b bs ih =>
      change xor b (p || q)::singleChange b p (bs++ys) =
        xor b (p || q)::(singleChange b p bs ++
          singleChange (memory b p bs).1 (memory b p bs).2 ys)
      rw [ih]

theorem change_append_one (p q : Bool) (xs : List Bool) (g : Bool) :
    singleChange p q (xs++[g])=singleChange p q xs ++ [xor g (force p q xs)] := by
  rw [change_append]
  rfl

theorem change_append_two (p q : Bool) (xs : List Bool) (g h : Bool) :
    singleChange p q (xs++[g,h])=singleChange p q xs ++
      [xor g (force p q xs),xor h (g || lastBit p xs)] := by
  rw [change_append]
  simp only [singleChange,force,memory_first]

theorem last_append_one (p : Bool) (xs : List Bool) (b : Bool) :
    lastBit p (xs++[b])=b := by
  induction xs generalizing p with
  | nil => rfl
  | cons a xs ih => exact ih a
theorem last_append_two (p : Bool) (xs : List Bool) (a b : Bool) :
    lastBit p (xs++[a,b])=b := by
  induction xs generalizing p with
  | nil => rfl
  | cons c xs ih => exact ih c

theorem A_append_two (u : List Bool) (g h : Bool) :
    A (u++[g,h])=A u++[halfBit u g,xor h (g || r u)] := by
  exact change_append_two false false u g h

theorem T_append_one (u : List Bool) (g : Bool) :
    T (u++[g])=T u++[xor g (drive u)] := by
  change singleChange true false (singleChange false false (u++[g]))=_
  rw [change_append_one,change_append_one]
  simp only [drive,A,singleStep,T,C,xor_three]

theorem T_append_two (u : List Bool) (g h : Bool) (hu : u≠[]) :
    T (u++[g,h])=T u++[xor g (drive u),
      xor (xor h (g || r u)) (halfBit u g || s u)] := by
  change C (A (u++[g,h]))=_
  rw [A_append_two]
  unfold C
  rw [change_append_two]
  have hl : lastBit true (A u)=s u :=
    last_default (A u) (A_nonempty hu) true false
  rw [hl]
  simp only [halfBit,drive,T,C,xor_three]

theorem titer_add (u : List Bool) (a b : Nat) :
    titer u (a+b)=titer (titer u a) b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg T ih

theorem titer_period (u : List Bool) (P : Nat) (hp : titer u P=u) (t : Nat) :
    titer u (t+P)=titer u t := by
  rw [Nat.add_comm,titer_add,hp]

theorem outR_period (u : List Bool) (P : Nat) (hp : titer u P=u) (t : Nat) :
    outR u (t+P)=outR u t := congrArg r (titer_period u P hp t)
theorem outS_period (u : List Bool) (P : Nat) (hp : titer u P=u) (t : Nat) :
    outS u (t+P)=outS u t := congrArg s (titer_period u P hp t)

theorem titer_append_one (u : List Bool) (g : Bool) (t : Nat) :
    titer (u++[g]) t=titer u t++[giter u g t] := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [titer,ih,T_append_one]
      rfl

theorem titer_append_two (u : List Bool) (g h : Bool) (hu : u≠[]) (t : Nat) :
    ∃ b, titer (u++[g,h]) t=titer u t++[giter u g t,b] := by
  induction t with
  | zero => exact ⟨h,rfl⟩
  | succ t ih =>
      obtain ⟨b,hb⟩ := ih
      rw [titer,hb,T_append_two _ _ _ (titer_nonempty hu t)]
      exact ⟨_,rfl⟩

theorem birth_eq (P : Nat) (u : List Bool) (g : Bool) :
    birth P u g=xor (giter u g P) g := by
  rw [birth,titer_append_one]
  unfold r
  rw [last_append_one]

theorem g_displacement (u : List Bool) (g : Bool) (P : Nat)
    (hp : titer u P=u) (t : Nat) :
    xor (giter u g (t+P)) (giter u g t)=birth P u g := by
  induction t with
  | zero => simpa only [Nat.zero_add,giter] using (birth_eq P u g).symm
  | succ t ih =>
      rw [show t+1+P=(t+P)+1 by omega]
      simp only [giter,titer_period u P hp t,xor_same_right]
      exact ih

theorem half_displacement (u : List Bool) (g : Bool) (P : Nat)
    (hp : titer u P=u) (t : Nat) :
    xor (halfBit (titer u (t+P)) (giter u g (t+P)))
      (halfBit (titer u t) (giter u g t))=birth P u g := by
  rw [titer_period u P hp t]
  simp only [halfBit,xor_same_right]
  exact g_displacement u g P hp t

theorem observation_ors (u : List Bool) (g h : Bool) (hu : u≠[]) (t : Nat) :
    xor (outR (u++[g,h]) t) (outS (u++[g,h]) t)=
      (giter u g t || outR u t) ∧
    xor (outS (u++[g,h]) t) (outR (u++[g,h]) (t+1))=
      (halfBit (titer u t) (giter u g t) || outS u t) := by
  obtain ⟨b,hb⟩ := titer_append_two u g h hu t
  have hr : outR (u++[g,h]) t=b := by
    unfold outR
    rw [hb]
    exact last_append_two false _ _ _
  have hs : outS (u++[g,h]) t=xor b (giter u g t || outR u t) := by
    unfold outS s
    rw [hb,A_append_two]
    exact last_append_two false _ _ _
  have hn : outR (u++[g,h]) (t+1)=xor (xor b (giter u g t || outR u t))
      (halfBit (titer u t) (giter u g t) || outS u t) := by
    unfold outR
    rw [titer,hb,T_append_two _ _ _ (titer_nonempty hu t)]
    exact last_append_two false _ _ _
  constructor
  · rw [hr,hs,xor_twice]
  · rw [hs,hn,xor_twice]

/-- Whole older return makes the appended penultimate displacement constant.
The observed differences are exactly the masked complements of the older outputs. -/
theorem masked_demodulation (u : List Bool) (g h : Bool) (P : Nat)
    (hu : u≠[]) (hp : titer u P=u) :
    ∀ t,
      demodR P (u++[g,h]) t=(birth P u g && !(outR u t)) ∧
      demodS P (u++[g,h]) t=(birth P u g && !(outS u t)) := by
  intro t
  constructor
  · dsimp only [demodR,delta]
    rw [(observation_ors u g h hu (t+P)).1,(observation_ors u g h hu t).1]
    rw [outR_period u P hp t,or_difference,g_displacement u g P hp t]
  · dsimp only [demodS,delta]
    rw [(observation_ors u g h hu (t+P)).2,(observation_ors u g h hu t).2]
    rw [outS_period u P hp t,or_difference,half_displacement u g P hp t]

/-- Pure periodicity makes the actual no-all-black witness occur within P. -/
theorem older_white_witness (u : List Bool) (P : Nat)
    (hu : u≠[]) (hP : 0<P) (hp : titer u P=u) :
    ∃ t, t<P ∧ (outR u t=false ∨ outS u t=false) := by
  apply Classical.byContradiction
  intro hn
  have hw : ∀ t, t<P → outR u t=true ∧ outS u t=true := by
    intro t ht
    constructor
    · cases hh : outR u t with
      | false => exact False.elim (hn ⟨t,ht,Or.inl hh⟩)
      | true => rfl
    · cases hh : outS u t with
      | false => exact False.elim (hn ⟨t,ht,Or.inr hh⟩)
      | true => rfl
  have hall : ∀ t, outR u t=true ∧ outS u t=true := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
        by_cases ht : t<P
        · exact hw t ht
        · have hi := ih (t-P) (by omega)
          have he : t=(t-P)+P := by omega
          rw [he,outR_period u P hp (t-P),outS_period u P hp (t-P)]
          exact hi
  exact not_always_black u hu hall

/-- A finite OR of the actual two observations detects the P-displacement.
P is a supplied return, not necessarily the least one. -/
theorem birth_detector (u : List Bool) (g h : Bool) (P : Nat)
    (hu : u≠[]) (hP : 0<P) (hp : titer u P=u) :
    birth P u g=(List.range P).any (fun t =>
      demodR P (u++[g,h]) t || demodS P (u++[g,h]) t) := by
  cases hb : birth P u g with
  | false =>
      symm
      apply List.any_eq_false.mpr
      intro t ht
      rw [(masked_demodulation u g h P hu hp t).1,
        (masked_demodulation u g h P hu hp t).2,hb]
      intro hc
      cases hc
  | true =>
      symm
      apply List.any_eq_true.mpr
      obtain ⟨t,ht,hw⟩ := older_white_witness u P hu hP hp
      refine ⟨t,List.mem_range.mpr ht,?_⟩
      rw [(masked_demodulation u g h P hu hp t).1,
        (masked_demodulation u g h P hu hp t).2,hb]
      rcases hw with hw | hw
      · rw [hw]
        rfl
      · rw [hw]
        cases outR u t <;> rfl

theorem demodulation_of_birth (u : List Bool) (g h : Bool) (P : Nat)
    (hu : u≠[]) (hp : titer u P=u) (hb : birth P u g=true) (t : Nat) :
    outR u t= !(demodR P (u++[g,h]) t) ∧
    outS u t= !(demodS P (u++[g,h]) t) := by
  have hh := masked_demodulation u g h P hu hp t
  rw [hb] at hh
  constructor
  · rw [hh.1]
    cases outR u t <;> rfl
  · rw [hh.2]
    cases outS u t <;> rfl

/-- Equal observations force equal flags; on a penultimate anti-period they
force equality of the older observations, even at different older widths. -/
theorem observe_birth_transfer (u v : List Bool) (g h g' h' : Bool) (P : Nat)
    (hu : u≠[]) (hv : v≠[]) (hP : 0<P)
    (hpu : titer u P=u) (hpv : titer v P=v)
    (heq : ∀ t, outR (u++[g,h]) t=outR (v++[g',h']) t ∧
      outS (u++[g,h]) t=outS (v++[g',h']) t) :
    birth P u g=birth P v g' ∧
      (birth P u g=true → ∀ t, outR u t=outR v t ∧ outS u t=outS v t) := by
  have hr : demodR P (u++[g,h])=demodR P (v++[g',h']) := by
    funext t
    simp only [demodR,delta,(heq (t+P)).1,(heq (t+P)).2,(heq t).1,(heq t).2]
  have hs : demodS P (u++[g,h])=demodS P (v++[g',h']) := by
    funext t
    simp only [demodS,delta,(heq (t+P)).2,(heq (t+P+1)).1,(heq t).2,(heq (t+1)).1]
  have hb : birth P u g=birth P v g' := by
    rw [birth_detector u g h P hu hP hpu,birth_detector v g' h' P hv hP hpv,hr,hs]
  refine ⟨hb,?_⟩
  intro hbu t
  have hbv : birth P v g'=true := hb.symm.trans hbu
  have h1 := demodulation_of_birth u g h P hu hpu hbu t
  have h2 := demodulation_of_birth v g' h' P hv hpv hbv t
  rw [hr,hs] at h1
  exact ⟨h1.1.trans h2.1.symm,h1.2.trans h2.2.symm⟩

end Rule30CAClockDemodulationResearch

