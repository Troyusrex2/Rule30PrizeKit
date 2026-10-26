module
public import Rule30CommonPastResearch

/-! The initial-subset problem is reduced to stability at the first mode
source. A general clock obstruction is proved separately. No unconditional
front-stability or subset-preservation theorem is claimed. -/
@[expose] public section
namespace Rule30FrontReductionResearch
open Ruliology.CellularAutomata
open Rule30CommonPastResearch
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def delta (a b : Nat → Nat → Bool) (t j : Nat) : Bool := xor (a t j) (b t j)
def InitSub (a b h : Nat → Nat → Bool) : Prop := ∀ j, SubAt a b h 0 j
def FrontStable (a b : Nat → Nat → Bool) : Prop :=
  ∀ h, Mode a b h → Common a b h → InitSub a b h → ∀ k,
    h 0 k=true → (∀ j, j<k → h 0 j=false) → ∀ t, delta a b t k=true
def Preserves (a b : Nat → Nat → Bool) : Prop :=
  ∀ h, Mode a b h → Common a b h → InitSub a b h → Subset a b h

theorem step_prefix (a b h : Nat → Bool) (k : Nat)
    (hz : ∀ i, i<k → h i=false) : ∀ j, j<k → modeStep a b h j=false := by
  intro j hj
  cases j with
  | zero => exact hz 0 hj
  | succ j =>
    cases j with
    | zero => simp [modeStep,hz 1 hj,hz 0 (by omega)]
    | succ j => simp [modeStep,hz (j+2) hj,hz (j+1) (by omega),hz j (by omega)]

theorem step_front (a b h : Nat → Bool) (k : Nat)
    (hz : ∀ i, i<k → h i=false) : modeStep a b h k=h k := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => simp [modeStep,hz 0 (by omega)]
    | succ k => simp [modeStep,hz (k+1) (by omega),hz k (by omega)]

theorem prefix_zero (a b h : Nat → Nat → Bool) (hh : Mode a b h) (k : Nat)
    (hz : ∀ j, j<k → h 0 j=false) : ∀ t j, j<k → h t j=false := by
  intro t
  induction t with
  | zero => exact hz
  | succ t ih =>
    intro j hj
    rw [hh t j]
    exact step_prefix (a t) (b t) (h t) k ih j hj

theorem first_source (a b h : Nat → Nat → Bool) (hh : Mode a b h) (k : Nat)
    (hz : ∀ j, j<k → h 0 j=false) (hk : h 0 k=true) : ∀ t, h t k=true := by
  intro t
  induction t with
  | zero => exact hk
  | succ t ih =>
    rw [hh t k,step_front (a t) (b t) (h t) k (prefix_zero a b h hh k hz t)]
    exact ih

theorem before_source (a b h : Nat → Nat → Bool) (hh : Mode a b h)
    (hw : Common a b h) (k : Nat) (hz : ∀ j, j<k → h 0 j=false)
    (hk : h 0 k=true) : ∀ t j, j+1=k → delta a b t j=false := by
  intro t j hj
  have hc := hw t j
  have hfront := first_source a b h hh k hz hk t
  have hzero := prefix_zero a b h hh k hz t j (by omega)
  simpa [GoodAt,delta,hj,hfront,hzero] using hc

theorem divided_local : ∀ l c r l' c' r' : Bool,
    xor (Rule30Jen.rule l c r) (Rule30Jen.rule l' c' r')=
      xor (xor l l') (xor ((!r') && xor c c') ((!c) && xor r r')) := by
  decide +kernel

theorem shuffle : ∀ a b c d : Bool, xor (xor a b) (xor c d)=
    xor (xor a c) (xor b d) := by decide +kernel

theorem delta_mode (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b) :
    Mode a b (delta a b) := by
  intro t j
  unfold delta
  rw [ha t j,hb t j]
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero => exact shuffle _ _ _ _
    | succ j => exact divided_local _ _ _ _ _ _

theorem combine_linear : ∀ a b l c r l' c' r' : Bool,
    xor (xor l l') (xor ((!b) && xor c c') ((!a) && xor r r'))=
      xor (xor l (xor ((!b) && c) ((!a) && r)))
        (xor l' (xor ((!b) && c') ((!a) && r'))) := by decide +kernel

theorem step_add (a b h g : Nat → Bool) (j : Nat) :
    modeStep a b (fun i => xor (h i) (g i)) j=
      xor (modeStep a b h j) (modeStep a b g j) := by
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero => exact shuffle _ _ _ _
    | succ j => exact combine_linear _ _ _ _ _ _ _ _

theorem mode_add (a b h g : Nat → Nat → Bool) (hh : Mode a b h) (hg : Mode a b g) :
    Mode a b (fun t j => xor (h t j) (g t j)) := by
  intro t j
  change xor (h (t+1) j) (g (t+1) j)=_
  rw [hh t j,hg t j,step_add]

theorem good_add_local : ∀ d e h k g l : Bool,
    (d && k)=(h && e) → (d && l)=(g && e) →
    (d && xor k l)=(xor h g && e) := by decide +kernel

theorem common_add (a b h g : Nat → Nat → Bool)
    (hh : Common a b h) (hg : Common a b g) :
    Common a b (fun t j => xor (h t j) (g t j)) := by
  intro t j
  exact good_add_local _ _ _ _ _ _ (hh t j) (hg t j)

theorem sub_add_local : ∀ d h g : Bool,
    (h && d)=h → (g && d)=g → (xor h g && d)=xor h g := by decide +kernel

def cut (k : Nat) (x : Nat → Bool) (j : Nat) : Bool := if k≤j then x j else false
def suffix (a b : Nat → Nat → Bool) (k t j : Nat) : Bool := cut k (delta a b t) j

theorem cut_zero (k : Nat) (x : Nat → Bool) : ∀ j, j<k → cut k x j=false := by
  intro j hj
  simp [cut,show ¬k≤j by omega]

theorem step_cut (a b x : Nat → Bool) (k : Nat)
    (hf : modeStep a b x k=x k) (hp : ∀ j, j+1=k → x j=false) :
    ∀ j, modeStep a b (cut k x) j=cut k (modeStep a b x) j := by
  intro j
  by_cases hj : j<k
  · rw [step_prefix a b (cut k x) k (cut_zero k x) j hj]
    simp [cut,show ¬k≤j by omega]
  by_cases he : j=k
  · subst j
    rw [step_front a b (cut k x) k (cut_zero k x)]
    simpa [cut] using hf.symm
  by_cases hn : j=k+1
  · subst j
    cases k with
    | zero => simp [cut,modeStep]
    | succ k =>
      have hz := hp k rfl
      simp [modeStep,cut,show ¬k+1≤k by omega,hz]
  · have hk : k+2≤j := by omega
    cases j with
    | zero => omega
    | succ j =>
      cases j with
      | zero => omega
      | succ j =>
        simp [modeStep,cut,show k≤j by omega,show k≤j+1 by omega,show k≤j+2 by omega]

theorem suffix_mode (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b) (k : Nat)
    (hf : ∀ t, delta a b t k=true)
    (hp : ∀ t j, j+1=k → delta a b t j=false) : Mode a b (suffix a b k) := by
  have hd := delta_mode a b ha hb
  intro t j
  change cut k (delta a b (t+1)) j=modeStep (a t) (b t) (cut k (delta a b t)) j
  rw [step_cut (a t) (b t) (delta a b t) k ?_ (hp t)]
  · congr 1
    funext i
    exact hd t i
  · rw [←hd t k,hf (t+1),hf t]

theorem suffix_common (a b : Nat → Nat → Bool) (k : Nat)
    (hp : ∀ t j, j+1=k → delta a b t j=false) : Common a b (suffix a b k) := by
  intro t j
  change (delta a b t j && suffix a b k t (j+1))=
    (suffix a b k t j && delta a b t (j+1))
  by_cases hj : k≤j
  · simp [suffix,cut,hj,show k≤j+1 by omega]
  · by_cases hn : k≤j+1
    · have he : j+1=k := by omega
      have hz := hp t j he
      simp [suffix,cut,hj,hn,hz]
    · simp [suffix,cut,hj,hn]

theorem suffix_subset (a b : Nat → Nat → Bool) (k : Nat) : Subset a b (suffix a b k) := by
  intro t j
  unfold SubAt suffix cut
  split <;> simp [delta]

theorem zero_mode (a b h : Nat → Nat → Bool) (hh : Mode a b h)
    (hz : ∀ j, h 0 j=false) : ∀ t j, h t j=false := by
  intro t
  induction t with
  | zero => exact hz
  | succ t ih =>
    intro j
    rw [hh t j]
    cases j with
    | zero => exact ih 0
    | succ j => cases j <;> simp [modeStep,ih]

theorem preservation_of_front (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (hfin : Finite (delta a b 0)) (hfront : FrontStable a b) : Preserves a b := by
  obtain ⟨N,hN⟩ := hfin
  have induction_step : ∀ n m, m+n=N → ∀ h, Mode a b h → Common a b h → InitSub a b h →
      (∀ j, j<m → h 0 j=false) → Subset a b h := by
    intro n
    induction n with
    | zero =>
      intro m hm h hh hw hs hz
      have hzero : ∀ j, h 0 j=false := by
        intro j
        by_cases hj : j<m
        · exact hz j hj
        · have hd := hN j (by omega)
          have he := hs j
          change (h 0 j && delta a b 0 j)=h 0 j at he
          rw [hd] at he
          simpa using he.symm
      intro t j
      simp [SubAt,zero_mode a b h hh hzero t j]
    | succ n ih =>
      intro m hm h hh hw hs hz
      cases he : h 0 m with
      | false =>
        apply ih (m+1) (by omega) h hh hw hs
        intro j hj
        by_cases hlt : j<m
        · exact hz j hlt
        · have : j=m := by omega
          simpa [this] using he
      | true =>
        have hf := hfront h hh hw hs m he hz
        have hp := before_source a b h hh hw m hz he
        let s := suffix a b m
        have sm : Mode a b s := suffix_mode a b ha hb m hf hp
        have sc : Common a b s := suffix_common a b m hp
        have ss : Subset a b s := suffix_subset a b m
        let r : Nat → Nat → Bool := fun t j => xor (h t j) (s t j)
        have rm : Mode a b r := mode_add a b h s hh sm
        have rc : Common a b r := common_add a b h s hw sc
        have rs : InitSub a b r := fun j => sub_add_local _ _ _ (hs j) (ss 0 j)
        have rz : ∀ j, j<m+1 → r 0 j=false := by
          intro j hj
          by_cases hlt : j<m
          · simp [r,s,suffix,cut,show ¬m≤j by omega,hz j hlt]
          · have hjm : j=m := by omega
            subst j
            simp [r,s,suffix,cut,he,hf 0]
        have rsub := ih (m+1) (by omega) r rm rc rs rz
        intro t j
        have hsum := sub_add_local _ _ _ (rsub t j) (ss t j)
        have hcancel : xor (r t j) (s t j)=h t j := cancel _ _
        change (xor (r t j) (s t j) && xor (a t j) (b t j))=xor (r t j) (s t j) at hsum
        rw [hcancel] at hsum
        exact hsum
  intro h hh hw hs
  exact induction_step N 0 (by omega) h hh hw hs (by intro j hj;omega)

theorem front_of_preservation (a b : Nat → Nat → Bool) (hp : Preserves a b) : FrontStable a b := by
  intro h hh hw hs k hk hz t
  have hs' := hp h hh hw hs t k
  have hf := first_source a b h hh k hz hk t
  simpa [SubAt,delta,hf] using hs'

theorem preservation_iff_front (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (hfin : Finite (delta a b 0)) : Preserves a b ↔ FrontStable a b :=
  ⟨front_of_preservation a b,preservation_of_front a b ha hb hfin⟩

/-! A temporal clock obstruction used at a possible first source. -/
theorem flip_gate : ∀ f fn x g : Bool,
    (fn && xor x g)=xor (f && x) (g && f) → (xor fn f && xor x g)=false := by
  decide +kernel

theorem same_of_xor : ∀ a b : Bool, xor a b=false → a=b := by decide +kernel

theorem clock_no_flips (f x g z : Nat → Bool) (P : Nat)
    (hx : ∀ t, x (t+1)=xor (x t) (g t))
    (hz : ∀ t, z t=(f t && x t))
    (hs : ∀ t, z (t+1)=xor (z t) (g t && f t))
    (hanti : ∀ t, x (t+P)=!x t)
    (hper : ∀ t, xor (f (t+P+1)) (f (t+P))=xor (f (t+1)) (f t)) :
    ∀ t, f t=f 0 := by
  have gate (t : Nat) : (xor (f (t+1)) (f t) && x (t+1))=false := by
    rw [hx]
    apply flip_gate
    rw [←hx,←hz,hs,hz]
  have hd (t : Nat) : xor (f (t+1)) (f t)=false := by
    have h0 := gate t
    have h1 := gate (t+P)
    rw [hper,show t+P+1=(t+1)+P by omega,hanti] at h1
    cases he : xor (f (t+1)) (f t) <;> cases hx' : x (t+1) <;> simp_all
  have step (t : Nat) : f (t+1)=f t := by
    exact same_of_xor _ _ (hd t)
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [step,ih]

theorem xor_slope : ∀ a b : Bool, xor (xor a b) a=b := by decide +kernel

theorem period_two_front_obstruction (f x q d z : Nat → Bool)
    (hq : ∀ t, q (t+1)=!q t) (hd : ∀ t, d (t+2)=d t)
    (hf : ∀ t, f (t+1)=xor (f t) ((!q t) && d t))
    (hx : ∀ t, x (t+1)=xor (x t) (!q t))
    (hz : ∀ t, z t=(f t && x t))
    (hs : ∀ t, z (t+1)=xor (z t) ((!q t) && f t)) : ∀ t, f t=f 0 := by
  have hq2 (t : Nat) : q (t+2)=q t := by
    rw [show t+2=(t+1)+1 by omega,hq,hq]
    exact Bool.not_not _
  have hanti (t : Nat) : x (t+2)=!x t := by
    rw [show t+2=(t+1)+1 by omega,hx,hx,hq]
    cases x t <;> cases q t <;> rfl
  have hper (t : Nat) : xor (f (t+2+1)) (f (t+2))=xor (f (t+1)) (f t) := by
    rw [hf (t+2),hf t,xor_slope,xor_slope,hq2,hd]
  exact clock_no_flips f x (fun t => !q t) z 2 hx hz hs hanti hper

theorem period_two_source_stable (a b h : Nat → Nat → Bool)
    (ha : Actual a) (hb : Actual b) (hh : Mode a b h) (hw : Common a b h)
    (hs0 : InitSub a b h) (n : Nat)
    (hzero : ∀ j, j<n+2 → h 0 j=false) (hsource : h 0 (n+2)=true)
    (hclock : ∀ t, a (t+1) (n+1)=!a t (n+1))
    (hright : ∀ t, delta a b (t+2) n=delta a b t n) :
    ∀ t, delta a b t (n+2)=true := by
  have hf := first_source a b h hh (n+2) hzero hsource
  have hp := prefix_zero a b h hh (n+2) hzero
  have hbz (t : Nat) : delta a b t (n+1)=false :=
    before_source a b h hh hw (n+2) hzero hsource t (n+1) (by omega)
  have heq (t : Nat) : b t (n+1)=a t (n+1) :=
    (same_of_xor _ _ (hbz t)).symm
  have hdm := delta_mode a b ha hb
  have ff (t : Nat) : delta a b (t+1) (n+2)=xor (delta a b t (n+2))
      ((!a t (n+1)) && delta a b t n) := by
    simpa [modeStep,hbz t] using hdm t (n+2)
  have xx (t : Nat) : h (t+1) (n+3)=xor (h t (n+3)) (!a t (n+1)) := by
    have he := hh t (n+1+2)
    simpa [modeStep,hf t,hp t (n+1) (by omega),heq t] using he
  have zz (t : Nat) : delta a b t (n+3)=(delta a b t (n+2) && h t (n+3)) := by
    have he := hw t (n+2)
    simpa [GoodAt,delta,hf t,show n+2+1=n+3 by omega] using he.symm
  have zs (t : Nat) : delta a b (t+1) (n+3)=xor (delta a b t (n+3))
      ((!a t (n+1)) && delta a b t (n+2)) := by
    have he := hdm t (n+1+2)
    simpa [modeStep,hbz t,heq t] using he
  have hconst := period_two_front_obstruction (fun t => delta a b t (n+2))
    (fun t => h t (n+3)) (fun t => a t (n+1)) (fun t => delta a b t n)
    (fun t => delta a b t (n+3)) hclock hright ff xx zz zs
  have hinit := hs0 (n+2)
  change (h 0 (n+2) && delta a b 0 (n+2))=h 0 (n+2) at hinit
  rw [hsource] at hinit
  intro t
  simpa only [Bool.true_and,hconst t] using hinit

/-! An explicit remaining background-only conjecture. This is a definition
of a hypothesis, not an axiom or an assertion that it holds. -/
def CollisionClock (a b : Nat → Nat → Bool) : Prop := ∀ n,
  (∀ t, delta a b t (n+1)=false) → delta a b 0 (n+2)=true →
  (∀ t, delta a b t (n+2)=true) ∨
    ((∀ t, a (t+1) (n+1)=!a t (n+1)) ∧
      (∀ t, delta a b (t+2) n=delta a b t n))

theorem front_of_collision_clock (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (hc : CollisionClock a b) : FrontStable a b := by
  intro h hh hw hs k hk hz
  have hi := hs k
  change (h 0 k && delta a b 0 k)=h 0 k at hi
  rw [hk] at hi
  have hinit : delta a b 0 k=true := by simpa using hi
  have hdm := delta_mode a b ha hb
  have hp := before_source a b h hh hw k hz hk
  cases k with
  | zero =>
    intro t
    induction t with
    | zero => exact hinit
    | succ t ih =>
      change delta a b (t+1) 0=true
      rw [hdm t 0]
      exact ih
  | succ k =>
    cases k with
    | zero =>
      have hsame (t : Nat) : delta a b (t+1) 1=delta a b t 1 := by
        simpa [modeStep,hp t 0 rfl] using hdm t 1
      intro t
      induction t with
      | zero => exact hinit
      | succ t ih => rw [hsame];exact ih
    | succ k =>
      rcases hc k (fun t => hp t (k+1) (by omega)) hinit with he|⟨ha2,hd2⟩
      · exact he
      · exact period_two_source_stable a b h ha hb hh hw hs k hz hk ha2 hd2

/-- Conditional on the stated collision-clock property; that property is open. -/
theorem preservation_of_collision_clock (a b : Nat → Nat → Bool)
    (ha : Actual a) (hb : Actual b) (hfin : Finite (delta a b 0))
    (hc : CollisionClock a b) : Preserves a b :=
  preservation_of_front a b ha hb hfin (front_of_collision_clock a b ha hb hc)

end Rule30FrontReductionResearch
