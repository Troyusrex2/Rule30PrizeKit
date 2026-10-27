module
public import Ruliology.CellularAutomata.Rule30ControlledResponse

/-! Marked oldest-birth exclusion for the actual head-first triangular
recurrence. The local theorem uses one shared trajectory and its own
half-shift. Finite-white applicability is provided by the official-state
bridge, not by identifying the auxiliary profile q with a genuine column. -/
@[expose] public section
namespace Rule30GatedDepthTwoResearch
open Ruliology.CellularAutomata
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def Actual (x : Nat → Nat → Bool) : Prop := ∀ i t,
  x i (t+1)=xor (x i t) (x (i+1) t || x (i+2) t)
def Period (P : Nat) (f : Nat → Bool) : Prop := ∀ t, f (t+P)=f t
def E (t : Nat) : Bool := decide (t%2=0)
def defect (x : Nat → Nat → Bool) (P i t : Nat) : Bool := xor (x i t) (x i (t+P))

theorem E_next (t : Nat) : E (t+1)= !(E t) := by
  unfold E
  have := Nat.mod_lt t (by decide : 0<2)
  by_cases h : t%2=0
  · have hn : (t+1)%2=1 := by omega
    simp [h,hn]
  · have ht : t%2=1 := by omega
    have hn : (t+1)%2=0 := by omega
    simp [ht,hn]

theorem E_period {P : Nat} (he : P%2=0) : Period P E := by
  intro t
  have hm : (t+P)%2=t%2 := by omega
  simp only [E,hm]

theorem constant_of_step {f : Nat → Bool} (hs : ∀ t, f (t+1)=f t) : ∀ t, f t=f 0 := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => exact (hs t).trans ih

theorem constant_driver_even {z : Nat → Bool} (b : Bool)
    (hz : ∀ t, z (t+1)=xor (z t) b) {P : Nat} (he : P%2=0) : z P=z 0 := by
  have hs : ∀ t, z (t+2)=z t := by
    intro t
    rw [show t+2=(t+1)+1 by omega,hz,hz]
    cases z t <;> cases b <;> rfl
  have hh : ∀ n, z (2*n)=z 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [show 2*(n+1)=2*n+2 by omega,hs,ih]
  simpa only [show 2*(P/2)=P by omega] using hh (P/2)

/-- Forward propagation suffices: no period of q or of the newer outputs
is assumed. The time-zero twin equality is deliberately not needed. -/
theorem marked_aux_exclusion (P : Nat) (he : P%2=0)
    (z f g k l m q : Nat → Bool)
    (za : ∀ t, z (t+P)= !(z t))
    (zs : ∀ t, z (t+1)=xor (z t) (f t || g t))
    (fs : ∀ t, f (t+1)=xor (f t) (g t || k t))
    (gs : ∀ t, g (t+1)=xor (g t) (k t || l t))
    (ks : ∀ t, k (t+1)=xor (k t) (l t || m t))
    (qs : ∀ t, q (t+1)=xor (q t) (f t))
    (mark : ∀ t, (E t && xor (f (t+1)) (f t)) =
      xor (f t) ((f t || g t) && xor (q (t+1)) (E t))) : False := by
  have contradiction_tail : ∀ (s : Nat) (b : Bool),
      (∀ t, s≤t → z (t+1)=xor (z t) b) → False := by
    intro s b hz
    have hh := constant_driver_even (z:=fun t => z (s+t)) b
      (fun t => by simpa only [Nat.add_assoc] using hz (s+t) (by omega)) he
    have aa := za s
    simp only [Nat.add_zero] at hh
    rw [hh] at aa
    cases h : z s <;> simp [h] at aa
  have gq : ∀ t, q t=true → g t=false := by
    intro t hq
    have hm := mark t
    rw [fs t,qs t,hq] at hm
    cases hgt : g t
    · rfl
    · cases hf : f t <;> cases hk : k t <;> cases he0 : E t <;>
        simp [hgt,hf,hk,he0] at hm
  have odd_step : ∀ t, t%2=1 → q t=true → q (t+1)=true := by
    intro t ht hq
    have hm := mark t
    have hs := qs t
    have et : E t=false := by simp [E,ht]
    rw [et] at hm
    cases hn : q (t+1)
    · cases hf : f t <;> cases hg : g t <;> simp [hn,hf,hg,hq] at hm hs
    · rfl
  have odd_pair : ∀ t, t%2=1 → q t=true → q (t+1)=true ∧ q (t+2)=true := by
    intro t ht hq
    have hn := odd_step t ht hq
    have hg0 := gq t hq
    have hg1 := gq (t+1) hn
    have hgs := gs t
    rw [hg0,hg1] at hgs
    have hk : k t=false := by
      cases hkt : k t <;> cases hlt : l t <;> simp [hkt,hlt] at hgs ⊢
    have hq0 := qs t
    rw [hq,hn] at hq0
    have hf0 : f t=false := by cases hft : f t <;> simp [hft] at hq0 ⊢
    have hf1 := fs t
    rw [hf0,hg0,hk] at hf1
    have hq2 := qs (t+1)
    rw [hn,hf1] at hq2
    exact ⟨hn,by simpa [Nat.add_assoc] using hq2⟩
  have odd_zero : ∀ t, t%2=1 → q t=false := by
    intro t ht
    cases hqt : q t
    · rfl
    · exfalso
      have allpair : ∀ n, q (t+2*n)=true ∧ q (t+2*n+1)=true := by
        intro n
        induction n with
        | zero => simpa using ⟨hqt,(odd_pair t ht hqt).1⟩
        | succ n ih =>
            have hh := odd_pair (t+2*n) (by omega) ih.1
            have hh2 := odd_pair (t+2*(n+1)) (by omega)
              (by simpa only [show t+2*(n+1)=t+2*n+2 by omega] using hh.2)
            exact ⟨by simpa only [show t+2*(n+1)=t+2*n+2 by omega] using hh.2,hh2.1⟩
      have allq : ∀ s, t≤s → q s=true := by
        intro s hs
        have hm := Nat.mod_lt (s-t) (by decide : 0<2)
        by_cases hp : (s-t)%2=0
        · have hh : s=t+2*((s-t)/2) := by omega
          rw [hh]
          exact (allpair ((s-t)/2)).1
        · have hh : s=t+2*((s-t)/2)+1 := by omega
          rw [hh]
          exact (allpair ((s-t)/2)).2
      have allf : ∀ s, t≤s → f s=false := by
        intro s hs
        have hh := qs s
        rw [allq s hs,allq (s+1) (by omega)] at hh
        cases hfs : f s <;> simp [hfs] at hh ⊢
      exact contradiction_tail t false (by
        intro s hs
        rw [zs,allf s hs,gq s (allq s hs)]
        cases z s <;> rfl)
  have odd_gk : ∀ t, t%2=1 → g t=false ∧ k t=false := by
    intro t ht
    have h0 := qs t
    have h1 := qs (t+1)
    rw [odd_zero t ht] at h0
    rw [show t+1+1=t+2 by omega,odd_zero (t+2) (by omega)] at h1
    have hf : f (t+1)=f t := by
      cases hq1 : q (t+1) <;> cases hf0 : f t <;> cases hf1 : f (t+1) <;>
        simp [hq1,hf0,hf1] at h0 h1 ⊢
    have hh := fs t
    rw [hf] at hh
    cases hft : f t <;> cases hgt : g t <;> cases hkt : k t <;>
      simp [hft,hgt,hkt] at hh ⊢
  have twins : ∀ t, 1≤t → g t=k t := by
    intro t ht1
    by_cases ht : t%2=1
    · rw [(odd_gk t ht).1,(odd_gk t ht).2]
    · have ht0 : t%2=0 := by omega
      let u := t-1
      have hu : u%2=1 := by dsimp [u]; omega
      have hu1 : u+1=t := by dsimp [u]; omega
      have hg := gs u
      have hk := ks u
      rw [(odd_gk u hu).1,(odd_gk u hu).2,hu1] at hg
      rw [(odd_gk u hu).2,hu1] at hk
      have hg0 := gs t
      rw [(odd_gk (t+1) (by omega)).1] at hg0
      cases hgt : g t <;> cases hkt : k t <;> cases hlt : l t <;>
        cases hlu : l u <;> cases hmu : m u <;> simp [hgt,hkt,hlt,hlu,hmu] at hg hk hg0 ⊢
  have even_step : ∀ t, 2≤t → t%2=0 → q t=true → q (t+2)=true := by
    intro t ht2 ht hq
    have hg := gq t hq
    have hk : k t=false := (twins t (by omega)).symm.trans hg
    have hf := fs t
    rw [hg,hk] at hf
    have hq0 := qs t
    have hq1 := qs (t+1)
    rw [odd_zero (t+1) (by omega)] at hq0 hq1
    rw [hq] at hq0
    have hft : f t=true := by cases hh : f t <;> simp [hh] at hq0 ⊢
    have hfn : f (t+1)=true := by simpa [hft] using hf
    rw [hfn] at hq1
    simpa [Nat.add_assoc] using hq1
  have eventual_q : ∃ s b, ∀ t, s≤t → q t=(E t && b) := by
    by_cases hex : ∃ t, 2≤t ∧ t%2=0 ∧ q t=true
    · obtain ⟨s,hs2,hs,hq⟩ := hex
      have hall : ∀ n, q (s+2*n)=true := by
        intro n
        induction n with
        | zero => simpa using hq
        | succ n ih =>
            simpa only [show s+2*(n+1)=s+2*n+2 by omega] using
              even_step (s+2*n) (by omega) (by omega) ih
      refine ⟨s,true,?_⟩
      intro t ht
      by_cases hp : t%2=0
      · have heq : t=s+2*((t-s)/2) := by omega
        have hh : q t=true := by rw [heq]; exact hall ((t-s)/2)
        simp [hh,E,hp]
      · rw [odd_zero t (by omega)]
        simp [E,hp]
    · refine ⟨2,false,?_⟩
      intro t ht
      have hh : q t=false := by
        cases hqt : q t
        · rfl
        · exfalso
          by_cases hp : t%2=0
          · exact hex ⟨t,ht,hp,hqt⟩
          · have hz := odd_zero t (by omega); simp [hqt] at hz
      simp [hh]
  obtain ⟨s,b,hq⟩ := eventual_q
  have fconst : ∀ t, s≤t → f t=b := by
    intro t ht
    have hh := qs t
    rw [hq t ht,hq (t+1) (by omega),E_next] at hh
    cases et : E t <;> cases ft : f t <;> cases bt : b <;> simp [et,ft,bt] at hh ⊢
  have gzero : ∀ t, s≤t → g t=false := by
    intro t ht
    have hh := fs t
    rw [fconst t ht,fconst (t+1) (by omega)] at hh
    cases bt : b <;> cases gt : g t <;> cases kt : k t <;> simp [bt,gt,kt] at hh ⊢
  exact contradiction_tail s b (by
    intro t ht
    rw [zs,fconst t ht,gzero t ht]
    simp)

theorem defect_step (x : Nat → Nat → Bool) (P : Nat) (ha : Actual x) (i t : Nat) :
    defect x P i (t+1)=xor (defect x P i t)
      (xor ((!x (i+2) t) && defect x P (i+1) t)
        ((!x (i+1) (t+P)) && defect x P (i+2) t)) := by
  unfold defect
  rw [show t+1+P=(t+P)+1 by omega,ha i t,ha i (t+P)]
  cases x i t <;> cases x i (t+P) <;> cases x (i+1) t <;>
    cases x (i+1) (t+P) <;> cases x (i+2) t <;> cases x (i+2) (t+P) <;> rfl

theorem defect_zero (x : Nat → Nat → Bool) (P i : Nat) (hp : Period P (x i)) :
    ∀ t, defect x P i t=false := by
  intro t
  unfold defect
  rw [hp t]
  cases x i t <;> rfl

theorem unit_antiperiod (x : Nat → Nat → Bool) (P i : Nat)
    (hu : ∀ t, defect x P i t=true) : ∀ t, x i (t+P)= !(x i t) := by
  intro t
  have hh := hu t
  unfold defect at hh
  cases ht : x i t <;> cases hp : x i (t+P) <;> simp [ht,hp] at hh ⊢

theorem depth_two_impossible (x : Nat → Nat → Bool) (P : Nat)
    (_hP : 0<P) (he : P%2=0) (ha : Actual x)
    (older : Period P (x 3))
    (hu : ∀ t, defect x P 2 t=true)
    (gate : ∀ t, defect x P 0 t=(E t && defect x P 1 t)) : False := by
  let y := defect x P 1
  let rr := fun t => xor (x 1 t) (x 2 t && y t)
  let q := fun t => xor (y t) (!(E t))
  have h3 := defect_zero x P 3 older
  have hy : ∀ t, y (t+1)=xor (y t) (!(x 3 t)) := by
    intro t
    dsimp only [y]
    rw [defect_step x P ha 1 t,hu t,h3 t]
    cases defect x P 1 t <;> cases x 3 t <;> cases x 2 (t+P) <;> rfl
  have h0 : ∀ t, defect x P 0 (t+1)=xor (defect x P 0 t) (!(rr t)) := by
    intro t
    rw [defect_step x P ha 0 t,hu t]
    dsimp only [rr,y,defect]
    cases x 1 t <;> cases x 1 (t+P) <;> cases x 2 t <;> rfl
  have rs : ∀ t, rr (t+1)=xor (rr t) (xor (x 3 t) ((x 3 t || x 4 t) && y (t+1))) := by
    intro t
    dsimp only [rr]
    rw [ha 1 t,ha 2 t,hy t]
    cases x 1 t <;> cases x 2 t <;> cases x 3 t <;> cases x 4 t <;> cases y t <;> rfl
  have rval : ∀ t, rr t=xor (E t) (xor (y t) (!(E t) && x 3 t)) := by
    intro t
    have hh := h0 t
    rw [gate (t+1),gate t,E_next] at hh
    change (!(E t) && y (t+1))=xor (E t && y t) (!(rr t)) at hh
    rw [hy] at hh
    cases et : E t <;> cases yt : y t <;> cases ft : x 3 t <;> cases rt : rr t <;> simp [et,yt,ft,rt] at hh ⊢
  have dr : ∀ t, xor (rr (t+1)) (rr t)=(E t && xor (x 3 (t+1)) (x 3 t)) := by
    intro t
    rw [rval (t+1),rval t,E_next,hy]
    cases E t <;> cases y t <;> cases x 3 t <;> cases x 3 (t+1) <;> rfl
  have qs : ∀ t, q (t+1)=xor (q t) (x 3 t) := by
    intro t
    dsimp only [q]
    rw [hy,E_next]
    cases E t <;> cases y t <;> cases x 3 t <;> rfl
  have qm : ∀ t, (E t && xor (x 3 (t+1)) (x 3 t)) =
      xor (x 3 t) ((x 3 t || x 4 t) && xor (q (t+1)) (E t)) := by
    intro t
    have hs : xor (rr (t+1)) (rr t)=xor (x 3 t) ((x 3 t || x 4 t) && y (t+1)) := by
      rw [rs]
      cases rr t <;> cases xor (x 3 t) ((x 3 t || x 4 t) && y (t+1)) <;> rfl
    have hqy : y (t+1)=xor (q (t+1)) (E t) := by
      dsimp only [q]
      rw [E_next]
      cases E t <;> cases y (t+1) <;> rfl
    exact (dr t).symm.trans (by simpa only [hqy] using hs)
  exact marked_aux_exclusion P he (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) q
    (unit_antiperiod x P 2 hu) (ha 2) (ha 3) (ha 4) (ha 5) qs qm

/-- Local oldest-unit exclusion. Every predecessor recurrence is shared and
literal; no assertion that arbitrary free boundary data is finite-white is made. -/
theorem unit_birth_not_near (x : Nat → Nat → Bool) (P j : Nat)
    (hP : 0<P) (he : P%2=0) (ha : Actual x)
    (older : ∀ i, j<i → Period P (x i))
    (hu : ∀ t, defect x P j t=true)
    (gate : ∀ t, defect x P 0 t=(E t && defect x P 1 t)) : 3≤j := by
  apply Classical.byContradiction
  intro hn
  have hj : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases hj with rfl | rfl | rfl
  · have hh := gate 0
    rw [hu 0,defect_zero x P 1 (older 1 (by decide)) 0] at hh
    simp [E] at hh
  · have h2 := defect_zero x P 2 (older 2 (by decide))
    have hzero : ∀ t, x 2 t=false := by
      intro t
      have hh := defect_step x P ha 0 t
      rw [gate (t+1),gate t,hu (t+1),hu t,h2 t,E_next] at hh
      cases et : E t <;> cases xt : x 2 t <;> cases xp : x 1 (t+P) <;> simp [et,xt,xp] at hh ⊢
    have hthree : ∀ t, x 3 t=false := by
      intro t
      have hh := ha 2 t
      rw [hzero t,hzero (t+1)] at hh
      cases ht : x 3 t <;> cases hk : x 4 t <;> simp [ht,hk] at hh ⊢
    have hs : ∀ t, x 1 (t+1)=x 1 t := by
      intro t
      rw [ha 1 t,hzero,hthree]
      cases x 1 t <;> rfl
    have hh := hu 0
    unfold defect at hh
    rw [Nat.zero_add,constant_of_step hs P] at hh
    cases hx : x 1 0 <;> simp [hx] at hh
  · exact (depth_two_impossible x P hP he ha (older 3 (by decide)) hu gate).elim

/-- Exact bridge to the catalog's head-first update, for any initial state. -/
def orbit (x : Rule30ControlledResponse.State) (i t : Nat) : Bool :=
  Rule30ControlledResponse.iterate x t i

theorem orbit_actual (x : Rule30ControlledResponse.State) : Actual (orbit x) := by
  intro i t
  rfl

/-- Autonomy turns an initial tail return into an all-time tail period. -/
theorem tail_period_from_return (x : Nat → Nat → Bool) (P d : Nat)
    (ha : Actual x) (hr : ∀ i, d≤i → x i P=x i 0) :
    ∀ i, d≤i → Period P (x i) := by
  intro i hi t
  induction t generalizing i with
  | zero => simpa using hr i hi
  | succ t ih =>
      rw [show t+1+P=(t+P)+1 by omega,ha i (t+P),ha i t,
        ih i hi,ih (i+1) (by omega),ih (i+2) (by omega)]

/-- The oldest initially failing coordinate has unit defect at every time.
The unit birth is derived, not supplied to the finite-word theorem. -/
theorem oldest_failure_unit (x : Nat → Nat → Bool) (P j : Nat)
    (ha : Actual x) (older : ∀ i, j<i → x i P=x i 0)
    (hne : x j P≠x j 0) : ∀ t, defect x P j t=true := by
  have hp := tail_period_from_return x P (j+1) ha (fun i hi => older i (by omega))
  have h1 := defect_zero x P (j+1) (hp (j+1) (by omega))
  have h2 := defect_zero x P (j+2) (hp (j+2) (by omega))
  have hz : defect x P j 0=true := by
    unfold defect
    simp only [Nat.zero_add]
    cases h0 : x j 0 <;> cases hP : x j P <;> simp [h0,hP] at hne ⊢
  intro t
  induction t with
  | zero => exact hz
  | succ t ih =>
      rw [defect_step x P ha j t,h1 t,h2 t,ih]
      simp

theorem short_tail_step_return (x : Nat → Nat → Bool) (P j : Nat)
    (hP : 0<P) (he : P%2=0) (ha : Actual x) (hj : j<3)
    (older : ∀ i, j<i → x i P=x i 0)
    (gate : ∀ t, defect x P 0 t=(E t && defect x P 1 t)) : x j P=x j 0 := by
  apply Classical.byContradiction
  intro hn
  have hp := tail_period_from_return x P (j+1) ha (fun i hi => older i (by omega))
  have bad := unit_birth_not_near x P j hP he ha
    (fun i hi => hp i (by omega)) (oldest_failure_unit x P j ha older hn) gate
  omega

/-- Three-coordinate return lifting for the marked defect boundary alone.
There is no whole-trajectory clock or full-gate premise. -/
theorem staggered_tail_return (x : Nat → Nat → Bool) (P : Nat)
    (hP : 0<P) (he : P%2=0) (ha : Actual x)
    (older : ∀ i, 3≤i → x i P=x i 0)
    (gate : ∀ t, defect x P 0 t=(E t && defect x P 1 t)) :
    ∀ i, x i P=x i 0 := by
  have h2 := short_tail_step_return x P 2 hP he ha (by decide)
    (fun i hi => older i (by omega)) gate
  have older1 : ∀ i, 1<i → x i P=x i 0 := by
    intro i hi
    by_cases heq : i=2
    · simpa only [heq] using h2
    · exact older i (by omega)
  have h1 := short_tail_step_return x P 1 hP he ha (by decide) older1 gate
  have older0 : ∀ i, 0<i → x i P=x i 0 := by
    intro i hi
    by_cases heq : i=1
    · simpa only [heq] using h1
    · exact older1 i (by omega)
  have h0 := short_tail_step_return x P 0 hP he ha (by decide) older0 gate
  intro i
  by_cases heq : i=0
  · simpa only [heq] using h0
  · exact older0 i (by omega)

open Rule30ControlledResponse

/-- Literal autonomy of the official head-first update, with arbitrary older data. -/
theorem iterate_tail (x : State) (d t i : Nat) :
    iterate x t (i+d)=iterate (fun k => x (k+d)) t i := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
      simp only [iterate,diagonal]
      rw [show i+d+1=(i+1)+d by omega,show i+d+2=(i+2)+d by omega,
        ih i,ih (i+1),ih (i+2)]

/-- A state with a returning tail at coordinate3 inherits the same positive
even return from its own all-time marked defect boundary. -/
theorem state_staggered_return (x : State) (P : Nat)
    (hP : 0<P) (he : P%2=0)
    (older : iterate (fun k => x (k+3)) P=(fun k => x (k+3)))
    (gate : ∀ t, defect (orbit x) P 0 t=(E t && defect (orbit x) P 1 t)) :
    iterate x P=x := by
  funext i
  apply staggered_tail_return (orbit x) P hP he (orbit_actual x) ?_ gate i
  intro k hk
  change iterate x P k=x k
  have hindex : k=(k-3)+3 := by omega
  rw [hindex,iterate_tail,older]

/-- The list is newest-first and its default older continuation is literally
white through the official `word` definition. The older word may be empty.
Only its supplied whole return is assumed; no clock of the extended word is. -/
theorem word_staggered_three_return (u : List Bool) (a b c : Bool) (P : Nat)
    (hP : 0<P) (he : P%2=0)
    (older : iterate (word u) P=word u)
    (gate : ∀ t, defect (orbit (word ([a,b,c]++u))) P 0 t=
      (E t && defect (orbit (word ([a,b,c]++u))) P 1 t)) :
    iterate (word ([a,b,c]++u)) P=word ([a,b,c]++u) := by
  apply state_staggered_return _ P hP he ?_ gate
  have htail : (fun k => word ([a,b,c]++u) (k+3))=word u := by
    funext k
    rw [word_append]
    rfl
  simpa only [htail] using older

end Rule30GatedDepthTwoResearch
