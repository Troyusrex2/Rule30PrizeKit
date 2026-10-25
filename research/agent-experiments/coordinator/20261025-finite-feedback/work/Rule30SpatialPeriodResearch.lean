import Rule30SpatialLiftingResearch

namespace Rule30SpatialPeriodResearch
open Rule30SpatialLiftingResearch
open Ruliology.CellularAutomata.Rule30ZeroBoundary

def stateAt (u : Nat → Bool) (s : State) : Nat → State
  | 0 => s
  | n+1 => step (u n) (stateAt u s n)

def inputWord (u : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n+1 => u n :: inputWord u n

theorem run_input (u : Nat → Bool) (n : Nat) (s : State) :
    runWord (inputWord u n) s = stateAt u s n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [inputWord,runWord,stateAt] using congrArg (step (u n)) ih

theorem input_zero (u : Nat → Bool) (n i : Nat) (hi : i<n) (hu : u i=false) :
    false ∈ inputWord u n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i=n
    · simp [inputWord,←h,hu]
    · have h' : i<n := by omega
      exact List.mem_cons_of_mem _ (ih h')

theorem stateAt_shift (u : Nat → Bool) (s : State) (n k : Nat) :
    stateAt u s (n+k) = stateAt (fun j => u (n+j)) (stateAt u s n) k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [Nat.add_assoc,stateAt] using congrArg (step (u (n+k))) ih

theorem period_mul (u : Nat → Bool) (p : Nat) (hp : ∀ n, u (n+p)=u n)
    (k j : Nat) : u (k*p+j)=u j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k+1)*p+j=(k*p+j)+p by rw [Nat.add_mul]; simp only [Nat.one_mul]; omega,hp,ih]

theorem stateAt_blocks (u : Nat → Bool) (p : Nat) (hp : ∀ n, u (n+p)=u n)
    (s : State) (k : Nat) :
    stateAt u s (k*p) = power (fun q => stateAt u q p) k s := by
  induction k with
  | zero => simp [stateAt,power]
  | succ k ih =>
    rw [show (k+1)*p=k*p+p by simp [Nat.add_mul],stateAt_shift]
    have hu : (fun j => u (k*p+j))=u := funext (period_mul u p hp k)
    rw [hu,ih]
    rfl

/-- A periodic binary driver with a zero gives an eventual period dividing
twice its own period, with transient at most three driver blocks. -/
theorem stateAt_period (u : Nat → Bool) (p : Nat)
    (hp : ∀ n, u (n+p)=u n) (hz : ∃ i, i<p ∧ u i=false)
    (s : State) (n : Nat) (hn : 3*p≤n) :
    stateAt u s (n+2*p)=stateAt u s n := by
  obtain ⟨i,hi,hui⟩ := hz
  have hword := input_zero u p i hi hui
  have hf : runWord (inputWord u p) = fun q => stateAt u q p := funext (run_input u p)
  have hb : stateAt u s (5*p)=stateAt u s (3*p) := by
    rw [stateAt_blocks u p hp,stateAt_blocks u p hp]
    simpa [hf] using word_power (inputWord u p) hword s
  obtain ⟨j,rfl⟩ : ∃ j, n=3*p+j := ⟨n-3*p,by omega⟩
  rw [show 3*p+j+2*p=5*p+j by omega,stateAt_shift,stateAt_shift]
  have hu5 : (fun j => u (5*p+j))=u := funext (period_mul u p hp 5)
  have hu3 : (fun j => u (3*p+j))=u := funext (period_mul u p hp 3)
  rw [hu5,hu3,hb]

theorem encode_injective (a b c d : Bool) :
    encode a b = encode c d ↔ a=c ∧ b=d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

def rowDriver (a : Nat → Bool) (D t : Nat) (n : Nat) : Bool :=
  recon a (D+n+1) (t+1)

theorem recon_stateAt (a : Nat → Bool) (D t n : Nat) :
    stateAt (rowDriver a D t) (encode (recon a D t) (recon a (D+1) t)) n =
    encode (recon a (D+n) t) (recon a (D+n+1) t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stateAt,ih,step_encode]
    simp only [rowDriver]
    simpa [Nat.add_assoc] using congrArg (encode (recon a (D+n+1) t))
      (recon_two a (D+n) t).symm

/-- Uniform spatial period lifting for the official sideways reconstruction:
if row t+1 has period p after depth D+1 and has a white cell in that block,
row t has period 2p after depth D+3p. -/
theorem recon_period_lift (a : Nat → Bool) (D t p : Nat)
    (hp : ∀ n, recon a (D+n+p+1) (t+1)=recon a (D+n+1) (t+1))
    (hz : ∃ i, i<p ∧ recon a (D+i+1) (t+1)=false)
    (n : Nat) (hn : 3*p≤n) :
    recon a (D+n+2*p) t = recon a (D+n) t := by
  have hup : ∀ n, rowDriver a D t (n+p)=rowDriver a D t n := by
    intro n
    simpa [rowDriver,Nat.add_assoc] using hp n
  have huz : ∃ i, i<p ∧ rowDriver a D t i=false := hz
  have h := stateAt_period (rowDriver a D t) p hup huz
    (encode (recon a D t) (recon a (D+1) t)) n hn
  rw [recon_stateAt,recon_stateAt] at h
  have h' := (encode_injective _ _ _ _).mp h
  simpa [Nat.add_assoc] using h'.1

end Rule30SpatialPeriodResearch
