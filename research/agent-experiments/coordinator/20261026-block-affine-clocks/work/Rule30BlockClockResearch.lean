module
public import Rule30CommonPastResearch

/-! A three-cell driven return map is affine after an even number of steps.
Its fourth power is the identity. This gives a uniform block clock bound.
The sharper diagonal period estimate is known in prose (placego G249);
this module supplies an independent kernel proof, not a new prize claim. -/
@[expose] public section
namespace Rule30BlockClockResearch
open Rule30CommonPastResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

abbrev Triple := Bool × Bool × Bool
abbrev Input := Bool × Bool

structure Affine where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  e : Bool
  f : Bool

def act (p : Affine) (s : Triple) : Triple :=
  (xor s.1 p.a,
   xor s.2.1 (xor p.b (p.c && s.1)),
   xor s.2.2 (xor (xor p.d (p.e && s.1)) (p.f && s.2.1)))

def identity : Affine := ⟨false,false,false,false,false,false⟩

def compose (p q : Affine) : Affine :=
  ⟨xor q.a p.a,
   xor (xor q.b p.b) (p.c && q.a),
   xor q.c p.c,
   xor (xor (xor q.d p.d) (p.e && q.a)) (p.f && q.b),
   xor (xor q.e p.e) (p.f && q.c),
   xor q.f p.f⟩

def fit (F : Triple → Triple) : Affine :=
  let z := F (false,false,false)
  let x := F (true,false,false)
  let y := F (false,true,false)
  ⟨z.1,z.2.1,xor x.2.1 z.2.1,z.2.2,xor x.2.2 z.2.2,xor y.2.2 z.2.2⟩

def gate (a u : Bool) (s : Triple) : Triple :=
  (xor s.1 a,xor s.2.1 (s.1 || u),xor s.2.2 (s.2.1 || s.1))

def pairAffine (a u b v : Bool) : Affine := fit (fun s => gate b v (gate a u s))

theorem identity_act (s : Triple) : act identity s=s := by
  rcases s with ⟨x,y,z⟩
  cases x <;> cases y <;> cases z <;> rfl

theorem compose_check : ∀ a b c d e f A B C D E F x y z : Bool,
    act (compose ⟨a,b,c,d,e,f⟩ ⟨A,B,C,D,E,F⟩) (x,y,z)=
      act ⟨a,b,c,d,e,f⟩ (act ⟨A,B,C,D,E,F⟩ (x,y,z)) := by decide +kernel

theorem compose_act (p q : Affine) (s : Triple) : act (compose p q) s=act p (act q s) := by
  cases p with
  | mk a b c d e f =>
    cases q with
    | mk A B C D E F =>
      rcases s with ⟨x,y,z⟩
      exact compose_check a b c d e f A B C D E F x y z

theorem pair_check : ∀ a u b v x y z : Bool,
    act (pairAffine a u b v) (x,y,z)=gate b v (gate a u (x,y,z)) := by decide +kernel

theorem pair_act (a u b v : Bool) (s : Triple) :
    act (pairAffine a u b v) s=gate b v (gate a u s) := by
  rcases s with ⟨x,y,z⟩
  exact pair_check a u b v x y z

theorem quartic_check : ∀ a b c d e f x y z : Bool,
    act ⟨a,b,c,d,e,f⟩ (act ⟨a,b,c,d,e,f⟩
      (act ⟨a,b,c,d,e,f⟩ (act ⟨a,b,c,d,e,f⟩ (x,y,z))))=(x,y,z) := by decide +kernel

theorem quartic_act (p : Affine) (s : Triple) : act p (act p (act p (act p s)))=s := by
  cases p with
  | mk a b c d e f =>
    rcases s with ⟨x,y,z⟩
    exact quartic_check a b c d e f x y z

def run (g : Nat → Input) : Nat → Triple → Triple
  | 0,s => s
  | k+1,s => gate (g k).1 (g k).2 (run g k s)

def returnAffine (g : Nat → Input) : Nat → Affine
  | 0 => identity
  | m+1 => compose (pairAffine (g (2*m)).1 (g (2*m)).2
      (g (2*m+1)).1 (g (2*m+1)).2) (returnAffine g m)

theorem return_act (g : Nat → Input) (m : Nat) (s : Triple) :
    act (returnAffine g m) s=run g (2*m) s := by
  induction m with
  | zero => exact identity_act s
  | succ m ih =>
    rw [returnAffine,compose_act,ih,pair_act]
    rw [show 2*(m+1)=2*m+1+1 by omega]
    rfl

theorem run_trajectory (g : Nat → Input) (c : Nat → Triple)
    (hc : ∀ t, c (t+1)=gate (g t).1 (g t).2 (c t)) (t k : Nat) :
    run (fun i => g (t+i)) k (c t)=c (t+k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run,ih]
    simpa only [Nat.add_assoc] using (hc (t+k)).symm

theorem periodic_mult (g : Nat → Input) (P : Nat) (hp : ∀ t, g (t+P)=g t) (n t : Nat) :
    g (t+n*P)=g t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul,show t+(n*P+P)=(t+n*P)+P by omega,hp,ih]

/-- Any periodic even-length driving word gives a four-period block return. -/
theorem even_block_period (g : Nat → Input) (c : Nat → Triple) (m : Nat)
    (hc : ∀ t, c (t+1)=gate (g t).1 (g t).2 (c t))
    (hp : ∀ t, g (t+2*m)=g t) : ∀ t, c (t+8*m)=c t := by
  intro t
  let P := 2*m
  let M := returnAffine (fun i => g (t+i)) m
  have hs (n : Nat) : (fun i => g ((t+n*P)+i))=(fun i => g (t+i)) := by
    funext i
    rw [show (t+n*P)+i=(t+i)+n*P by omega]
    exact periodic_mult g P hp n (t+i)
  have chunk (n : Nat) : c (t+(n+1)*P)=act M (c (t+n*P)) := by
    calc
      c (t+(n+1)*P)=c ((t+n*P)+P) := by rw [Nat.succ_mul];congr 1 <;> omega
      _=run (fun i => g ((t+n*P)+i)) P (c (t+n*P)) := (run_trajectory g c hc (t+n*P) P).symm
      _=run (fun i => g (t+i)) P (c (t+n*P)) := by rw [hs]
      _=act M (c (t+n*P)) := (return_act _ m _).symm
  have h0 := chunk 0
  have h1 := chunk 1
  have h2 := chunk 2
  have h3 := chunk 3
  simp only [Nat.zero_mul,Nat.add_zero] at h0
  rw [h2,h1,h0] at h3
  rw [quartic_act] at h3
  simpa only [P,show 4*(2*m)=8*m by omega] using h3

theorem two_step_local_check : ∀ v w x y z : Bool,
    xor (xor z (y || x)) ((xor y (x || w)) || (xor x (w || v)))=
      xor z ((w || v) && !(xor x y)) := by decide +kernel

/-- The two-step rule is affine in the three latest cells once the earlier pair is fixed. -/
theorem actual_two_step (a : Nat → Nat → Bool) (ha : Actual a) (n t : Nat) :
    a (t+2) (n+4)=xor (a t (n+4))
      ((a t (n+1) || a t n) && !(xor (a t (n+2)) (a t (n+3)))) := by
  rw [show t+2=(t+1)+1 by omega,ha (t+1) (n+4)]
  change xor (a (t+1) (n+4)) (a (t+1) (n+3) || a (t+1) (n+2))=_
  rw [ha t (n+4),ha t (n+3),ha t (n+2)]
  exact two_step_local_check _ _ _ _ _

def PrefixPeriod (a : Nat → Nat → Bool) (n P : Nat) : Prop :=
  ∀ j, j<n → ∀ t, a (t+P) j=a t j

theorem actual_block (a : Nat → Nat → Bool) (ha : Actual a) (n t : Nat) :
    (a (t+1) (n+2),a (t+1) (n+3),a (t+1) (n+4))=
      gate (a t (n+1) || a t n) (a t (n+1))
        (a t (n+2),a t (n+3),a t (n+4)) := by
  rw [ha t (n+2),ha t (n+3),ha t (n+4)]
  rfl

/-- Three more depths multiply an even prefix clock by at most four. -/
theorem prefix_three_step (a : Nat → Nat → Bool) (ha : Actual a) (n m : Nat)
    (hp : PrefixPeriod a (n+2) (2*m)) : PrefixPeriod a (n+5) (8*m) := by
  let g := fun t => (a t (n+1) || a t n,a t (n+1))
  let c := fun t => (a t (n+2),a t (n+3),a t (n+4))
  have hg (t : Nat) : g (t+2*m)=g t := by
    dsimp [g]
    rw [hp (n+1) (by omega) t,hp n (by omega) t]
  have hc := even_block_period g c m (actual_block a ha n) hg
  intro j hj t
  by_cases he : j<n+2
  · have h1 := Ruliology.CellularAutomata.Rule30Diagonals.periodic_double
      (f:=fun s => a s j) (L:=2*m) (hp j he)
    have h2 := Ruliology.CellularAutomata.Rule30Diagonals.periodic_double
      (f:=fun s => a s j) (L:=2*(2*m)) h1 t
    simpa only [show 2*(2*(2*m))=8*m by omega] using h2
  · have h := hc t
    by_cases h2 : j=n+2
    · subst j
      exact congrArg (fun s : Triple => s.1) h
    · by_cases h3 : j=n+3
      · subst j
        exact congrArg (fun s : Triple => s.2.1) h
      · have h4 : j=n+4 := by omega
        subst j
        exact congrArg (fun s : Triple => s.2.2) h

theorem base_involution : ∀ x y z : Bool,
    gate false false (gate false false (x,y,z))=(x,y,z) := by decide +kernel

theorem prefix_three_base (a : Nat → Nat → Bool) (ha : Actual a) : PrefixPeriod a 3 2 := by
  let c := fun t => (a t 0,a t 1,a t 2)
  have hs (t : Nat) : c (t+1)=gate false false (c t) := by
    simp only [c,gate,ha t 0,ha t 1,ha t 2,march,Bool.or_false,Bool.xor_false]
  have ht (t : Nat) : c (t+2)=c t := by
    rw [show t+2=(t+1)+1 by omega,hs,hs]
    exact base_involution _ _ _
  intro j hj t
  cases j with
  | zero => exact congrArg (fun s : Triple => s.1) (ht t)
  | succ j =>
    cases j with
    | zero => exact congrArg (fun s : Triple => s.2.1) (ht t)
    | succ j =>
      have hz : j=0 := by omega
      subst j
      exact congrArg (fun s : Triple => s.2.2) (ht t)

theorem prefix_two_base (a : Nat → Nat → Bool) (ha : Actual a) : PrefixPeriod a 2 2 :=
  fun j hj => prefix_three_base a ha j (by omega)

theorem prefix_four_base (a : Nat → Nat → Bool) (ha : Actual a) : PrefixPeriod a 4 4 := by
  intro j hj
  by_cases he : j<3
  · exact Ruliology.CellularAutomata.Rule30Diagonals.periodic_double
      (f:=fun s => a s j) (L:=2) (prefix_three_base a ha j he)
  · have h3 : j=3 := by omega
    subst j
    have hx (t : Nat) : a (t+1) 3=xor (a t 3) (a t 2 || a t 1) := ha t 3
    have hg (t : Nat) : (a (t+2) 2 || a (t+2) 1)=(a t 2 || a t 1) := by
      rw [prefix_three_base a ha 2 (by omega) t,prefix_three_base a ha 1 (by omega) t]
    exact Ruliology.CellularAutomata.Rule30Diagonals.xor_accum_periodic
      (x:=fun s => a s 3) (g:=fun s => a s 2 || a s 1) (L:=2) hx hg

theorem prefix_exponent_step (a : Nat → Nat → Bool) (ha : Actual a) (n e : Nat)
    (hp : PrefixPeriod a (n+2) (2^(e+1))) : PrefixPeriod a (n+5) (2^(e+3)) := by
  have h2 : 2*(2^e)=2^(e+1) := by rw [Nat.pow_succ];omega
  have h8 : 8*(2^e)=2^(e+3) := by
    rw [Nat.pow_add]
    change 8*(2^e)=(2^e)*8
    omega
  have h := prefix_three_step a ha n (2^e) (by simpa only [h2] using hp)
  simpa only [h8] using h

theorem prefix_clock_families (a : Nat → Nat → Bool) (ha : Actual a) : ∀ k,
    PrefixPeriod a (3*k+2) (2^(2*k+1)) ∧
    PrefixPeriod a (3*k+3) (2^(2*k+1)) ∧
    PrefixPeriod a (3*k+4) (2^(2*k+2)) := by
  intro k
  induction k with
  | zero => exact ⟨prefix_two_base a ha,prefix_three_base a ha,prefix_four_base a ha⟩
  | succ k ih =>
    constructor
    · have h := prefix_exponent_step a ha (3*k) (2*k) ih.1
      simpa only [show 3*(k+1)+2=3*k+5 by omega,show 2*(k+1)+1=2*k+3 by omega] using h
    · constructor
      · have h := prefix_exponent_step a ha (3*k+1) (2*k) ih.2.1
        simpa only [show 3*(k+1)+3=3*k+6 by omega,show 2*(k+1)+1=2*k+3 by omega] using h
      · have h := prefix_exponent_step a ha (3*k+2) (2*k+1) ih.2.2
        simpa only [show 3*(k+1)+4=3*k+7 by omega,show 2*(k+1)+2=2*k+4 by omega] using h

/-- The known sharper right-prefix clock, independently proved here. -/
theorem actual_periodic_tighter (a : Nat → Nat → Bool) (ha : Actual a) :
    ∀ j t, a (t+2^((2*j+1)/3)) j=a t j := by
  intro j t
  by_cases hz : j=0
  · subst j
    exact ha t 0
  · have hr : j%3<3 := Nat.mod_lt j (by decide)
    have hj := Nat.mod_add_div j 3
    by_cases h1 : j%3=1
    · have he : (2*j+1)/3=2*(j/3)+1 := by omega
      rw [he]
      exact (prefix_clock_families a ha (j/3)).1 j (by omega) t
    · by_cases h2 : j%3=2
      · have he : (2*j+1)/3=2*(j/3)+1 := by omega
        rw [he]
        exact (prefix_clock_families a ha (j/3)).2.1 j (by omega) t
      · have he : (2*j+1)/3=2*(j/3-1)+2 := by omega
        rw [he]
        exact (prefix_clock_families a ha (j/3-1)).2.2 j (by omega) t

theorem xor_left_cancel_check : ∀ a x y : Bool, xor a x=xor a y → x=y := by decide +kernel

/-- Retains ALL-TIME subset: this does not prove initial-subset preservation. -/
theorem supported_common_mode_periodic_tighter (a b h : Nat → Nat → Bool)
    (ha : Actual a) (hh : Mode a b h) (hw : Common a b h) (hs : Subset a b h) :
    ∀ j t, h (t+2^((2*j+1)/3)) j=h t j := by
  have hc := actual_recombination a b h ha hh hw hs
  have hp := actual_periodic_tighter _ hc
  intro j t
  have he := hp j t
  change xor (a (t+2^((2*j+1)/3)) j) (h (t+2^((2*j+1)/3)) j)=xor (a t j) (h t j) at he
  rw [actual_periodic_tighter a ha j t] at he
  exact xor_left_cancel_check _ _ _ he

end Rule30BlockClockResearch
