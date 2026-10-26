module
public import Rule30OrClockObserverResearch

/-! A computable clock-sensitive observer in the clock-extending case.
It scans aligned observations until their first mismatch. The zero-in-mask
and clock premises are explicit; the plateau case is not resolved. -/
@[expose] public section
namespace Rule30ClockSearchResearch
open Rule30CommonPastResearch
set_option maxHeartbeats 4000000

def scan (P : Nat) : Nat → (Nat → Bool) → Bool
  | 0,_ => false
  | n+1,r => if r 0==r P then !(scan P n (fun t => r (t+1))) else r 0

theorem scan_correct (n P : Nat) (r g h : Nat → Bool)
    (ho : ∀ t, r t=(g t || h t))
    (hm : ∀ t, (r t==r (t+P))=h t)
    (hs : ∀ t, h t=true → g (t+1)= !g t)
    (hz : ∃ t, t<n ∧ h t=false) : scan P n r=g 0 := by
  induction n generalizing r g h with
  | zero => obtain ⟨t,ht,_⟩ := hz;omega
  | succ n ih =>
    have hm0 : (r 0==r P)=h 0 := by simpa only [Nat.zero_add] using hm 0
    cases hh : h 0 with
    | false => rw [scan,hm0,hh];simp [ho 0,hh]
    | true =>
      have hz' : ∃ t, t<n ∧ h (t+1)=false := by
        obtain ⟨t,ht,he⟩ := hz
        have hn : t≠0 := by
          intro ht0;rw [ht0,hh] at he;cases he
        have hp : 0<t := by omega
        refine ⟨t-1,by omega,?_⟩
        simpa only [show t-1+1=t by omega] using he
      have hi := ih (fun t => r (t+1)) (fun t => g (t+1)) (fun t => h (t+1))
        (fun t => ho (t+1))
        (by intro t;simpa only [show t+P+1=t+1+P by omega] using hm (t+1))
        (fun t => hs (t+1)) hz'
      have hg := hs 0 hh
      rw [scan,hm0,hh]
      simpa [hi,hg] using (show !(!g 0)=g 0 from Bool.not_not _)

theorem scan_congr (n P : Nat) (r s : Nat → Bool)
    (he : ∀ t, t<n+P → r t=s t) : scan P n r=scan P n s := by
  induction n generalizing r s with
  | zero => rfl
  | succ n ih =>
    have h0 := he 0 (by omega)
    have hP := he P (by omega)
    have ht := ih (fun t => r (t+1)) (fun t => s (t+1)) (by intro t ht;exact he (t+1) (by omega))
    simp only [scan,h0,hP,ht]

theorem mask_from_anti (g h : Nat → Bool) (P : Nat)
    (hg : ∀ t, g (t+P)=xor (g t) true) (hh : ∀ t, h (t+P)=h t) :
    ∀ t, ((g t || h t)==(g (t+P) || h (t+P)))=h t := by
  intro t;rw [hg t,hh t]
  cases g t <;> cases h t <;> rfl

theorem anti_clock_scan (g h k : Nat → Bool) (n P : Nat)
    (gs : ∀ t, g (t+1)=xor (g t) (h t || k t))
    (hg : ∀ t, g (t+P)=xor (g t) true) (hh : ∀ t, h (t+P)=h t)
    (hz : ∃ t, t<n ∧ h t=false) :
    scan P n (fun t => g t || h t)=g 0 := by
  apply scan_correct n P _ g h (fun _ => rfl) (mask_from_anti g h P hg hh)
  · intro t ht;rw [gs t,ht]
    cases g t <;> rfl
  · exact hz

theorem actual_clock_scan (a : Nat → Nat → Bool) (ha : Actual a) (j n P : Nat)
    (hg : ∀ t, a (t+P) (j+2)=xor (a t (j+2)) true)
    (hh : ∀ t, a (t+P) (j+1)=a t (j+1))
    (hz : ∃ t, t<n ∧ a t (j+1)=false) :
    scan P n (fun t => a t (j+2) || a t (j+1))=a 0 (j+2) := by
  exact anti_clock_scan _ _ (fun t => a t j) n P (fun t => ha t (j+2)) hg hh hz

theorem periodic_add_mul (h : Nat → Bool) (P : Nat)
    (hp : ∀ t, h (t+P)=h t) (t k : Nat) : h (t+P*k)=h t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,show t+(P*k+P)=(t+P*k)+P by omega,hp,ih]

theorem periodic_mod (h : Nat → Bool) (P : Nat)
    (hp : ∀ t, h (t+P)=h t) (t : Nat) : h (t%P)=h t := by
  have he := periodic_add_mul h P hp (t%P) (t/P)
  rw [Nat.mod_add_div] at he
  exact he.symm

/-- No supplied zero location is needed: a positive mask period bounds the scan. -/
theorem anti_clock_window (g h k : Nat → Bool) (P : Nat) (hP : 0<P)
    (gs : ∀ t, g (t+1)=xor (g t) (h t || k t))
    (hg : ∀ t, g (t+P)=xor (g t) true) (hh : ∀ t, h (t+P)=h t)
    (hz : ∃ t, h t=false) : scan P P (fun t => g t || h t)=g 0 := by
  obtain ⟨t,ht⟩ := hz
  apply anti_clock_scan g h k P P gs hg hh
  exact ⟨t%P,Nat.mod_lt _ hP,by rw [periodic_mod h P hh t];exact ht⟩

theorem actual_clock_window (a : Nat → Nat → Bool) (ha : Actual a) (j P : Nat)
    (hP : 0<P) (hg : ∀ t, a (t+P) (j+2)=xor (a t (j+2)) true)
    (hh : ∀ t, a (t+P) (j+1)=a t (j+1)) (hz : ∃ t, a t (j+1)=false) :
    scan P P (fun t => a t (j+2) || a t (j+1))=a 0 (j+2) := by
  exact anti_clock_window _ _ (fun t => a t j) P hP (fun t => ha t (j+2)) hg hh hz

def decodeHead (P : Nat) (c : Nat → Bool) : Bool :=
  scan P P (fun t => xor (c (t+1)) (c t))

theorem head_clock_window (c g h k : Nat → Bool) (P : Nat) (hP : 0<P)
    (cs : ∀ t, c (t+1)=xor (c t) (g t || h t))
    (gs : ∀ t, g (t+1)=xor (g t) (h t || k t))
    (hg : ∀ t, g (t+P)=xor (g t) true) (hh : ∀ t, h (t+P)=h t)
    (hz : ∃ t, h t=false) : decodeHead P c=g 0 := by
  have he : (fun t => xor (c (t+1)) (c t))=(fun t => g t || h t) := by
    funext t;rw [cs t]
    cases c t <;> cases (g t || h t) <;> rfl
  rw [decodeHead,he]
  exact anti_clock_window g h k P hP gs hg hh hz

theorem decodeHead_congr (c d : Nat → Bool) (P : Nat)
    (he : ∀ t, t≤2*P → c t=d t) : decodeHead P c=decodeHead P d := by
  apply scan_congr P P
  intro t ht
  rw [he (t+1) (by omega),he t (by omega)]

theorem actual_head_clock_window (a : Nat → Nat → Bool) (ha : Actual a) (j P : Nat)
    (hP : 0<P) (hg : ∀ t, a (t+P) (j+2)=xor (a t (j+2)) true)
    (hh : ∀ t, a (t+P) (j+1)=a t (j+1)) (hz : ∃ t, a t (j+1)=false) :
    decodeHead P (fun t => a t (j+3))=a 0 (j+2) := by
  exact head_clock_window (fun t => a t (j+3)) (fun t => a t (j+2))
    (fun t => a t (j+1)) (fun t => a t j) P hP
    (fun t => ha t (j+3)) (fun t => ha t (j+2)) hg hh hz

end Rule30ClockSearchResearch
