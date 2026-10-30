module
public import ReturnSections
@[expose] public section
namespace WordBoundary
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration LeakDescent ReturnActions ReturnSections
open ReturnSections.State

theorem prefix_multiple (n P : Nat) (x : Code)
    (fixed : AgreeBelow n (iter P x) x) :
    ∀ q,AgreeBelow n (iter (q*P) x) x := by
  intro q
  induction q with
  | zero => intro j hj;simp only [Nat.zero_mul,iter]
  | succ q ih =>
    intro j hj
    rw [show (q+1)*P=q*P+P by rw [Nat.add_mul,Nat.one_mul],iter_add]
    exact (iter_agree ih P j hj).trans (fixed j hj)

theorem prefix_mod (n P : Nat) (x : Code)
    (fixed : AgreeBelow n (iter P x) x) (t : Nat) :
    AgreeBelow n (iter t x) (iter (t%P) x) := by
  have h:=iter_agree (prefix_multiple n P x fixed (t/P)) (t%P)
  intro j hj
  have eq:=h j hj
  rw [←iter_add] at eq
  have decomp : t/P*P+t%P=t := by simpa only [Nat.mul_comm] using Nat.div_add_mod t P
  rw [decomp] at eq
  exact eq

theorem temporal_eq_states (n P : Nat) (x y : Code)
    (equal : temporalWord n x P=temporalWord n y P) :
    ∀ t,t<P → stateAfter A (iter t x) n=stateAfter A (iter t y) n := by
  induction P with
  | zero => intro t ht;omega
  | succ P ih =>
    have pair:=List.cons.inj equal
    intro t ht
    by_cases low : t<P
    · exact ih pair.2 t low
    · have eq : t=P := by omega
      subst t;exact pair.1

/-- Equal actual return words match the boundary state at EVERY tick, not
only the P-sampled return maps. Prefix periodicity suffices; tails are free. -/
theorem memory_equal_all (n P : Nat) (hP : 0<P) (x y : Code)
    (fx : AgreeBelow n (iter P x) x) (fy : AgreeBelow n (iter P y) y)
    (equal : returnWord n P x=returnWord n P y) :
    ∀ t,stateAfter A (iter t x) n=stateAfter A (iter t y) n := by
  rw [returnWord_eq,returnWord_eq,sections_temporal,sections_temporal] at equal
  intro t
  have mid:=temporal_eq_states n P x y equal (t%P) (Nat.mod_lt _ hP)
  exact (after_agree A _ _ n (prefix_mod n P x fx t)).trans
    (mid.trans (after_agree A _ _ n (prefix_mod n P y fy t)).symm)

theorem joined_memory (n : Nat) (x z : Code) (t : Nat) :
    stateAfter A (iter t (join n x z)) n=stateAfter A (iter t x) n := by
  apply after_agree
  exact iter_agree (fun j hj => join_low n x z j hj) t

/-- The exact cut is n: no 2P enlargement is needed for word equality.
This is stronger information than equality of the sampled return functions. -/
theorem shared_words_confine_at_cut (n P : Nat) (hP : 0<P) (x y z : Code)
    (fx : AgreeBelow n (iter P x) x) (fy : AgreeBelow n (iter P y) y)
    (equal : returnWord n P x=returnWord n P y) :
    ∀ t,drop n (iter t (join n x z))=drop n (iter t (join n y z)) := by
  have memory:=memory_equal_all n P hP x y fx fy equal
  intro t
  induction t with
  | zero => exact (drop_join n x z).trans (drop_join n y z).symm
  | succ t ih =>
    change drop n (T (iter t (join n x z)))=drop n (T (iter t (join n y z)))
    rw [←act_A (iter t (join n x z)),←act_A (iter t (join n y z)),drop_act,drop_act,
      joined_memory,joined_memory,memory t,ih]

def PeriodicMemory (n d : Nat) (x : Code) : Prop :=
  ∀ t,stateAfter A (iter (t+d) x) n=stateAfter A (iter t x) n

def PrefixPeriodReflection : Prop := ∀ (n d : Nat) (x : Code),
  0<n → 0<d → x 0=true → PeriodicMemory n d x → AgreeBelow n (iter d x) x

/-- Still conditional: full source-word injectivity would imply the
narrower within-orbit period-reflection property. -/
theorem reflection_of_word_injective (inj : AllReturnWordsInjective) :
    PrefixPeriodReflection := by
  intro n d x hn hd hx periodic
  have words : returnWord n (2^n) (iter d x)=returnWord n (2^n) x := by
    rw [returnWord_eq,returnWord_eq,sections_temporal,sections_temporal]
    have states : ∀ P,temporalWord n (iter d x) P=temporalWord n x P := by
      intro P
      induction P with
      | zero => rfl
      | succ P ih =>
        change stateAfter A (iter P (iter d x)) n :: _=stateAfter A (iter P x) n :: _
        rw [←iter_add]
        rw [show d+P=P+d by omega,periodic P,ih]
    exact states _
  exact inj n (2^n) (iter d x) x hn (Nat.two_pow_pos n)
    (by simpa only [iter_zero] using hx) hx
    (prefix_period n _) (prefix_period n _) words

end WordBoundary
