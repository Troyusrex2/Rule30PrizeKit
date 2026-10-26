import SafeClockEntry

/-! Intrinsic whole-word clocks for the Safe-to-height-two entry reduction.
The clock is the least POSITIVE EVEN return of the whole finite word.
It is not the least period of a column. The plateau alternative is retained. -/
namespace SafeClockDichotomy
open CedarSafetySoundness CedarSafety HeightOneLogic HeightOneSemantics
open HeightOneTransfer HeightOnePeriodicity SafeClockEntry
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem double_return (u : List Bool) (P : Nat) (hu : evolution P u=u) :
    evolution (2*P) u=u := by
  rw [show 2*P=P+P by omega,evolution_add,hu,hu]

theorem extension_double_return (u : List Bool) (v : Bool) (P : Nat)
    (hu : evolution P u=u) : evolution (2*P) (u++[v])=u++[v] := by
  by_cases hr : evolution P (u++[v])=u++[v]
  · exact double_return (u++[v]) P hr
  have ha := nonreturn_leaf_antiperiod u v P hu hr
  have hv : tr (u++[v]) (2*P)=v := by
    have h0 := ha 0
    have hP := ha P
    rw [show P+P=2*P by omega] at hP
    simp only [Nat.zero_add] at h0
    rw [h0,Bool.not_not,tr_snoc] at hP
    rw [tr_snoc]
    exact hP
  rw [evolution_snoc,double_return u P hu,hv]

theorem exists_even_whole_return (xs : List Bool) :
    ∃ P : Nat, 0<P ∧ Even P ∧ evolution P xs=xs := by
  have all : ∀ n : Nat, ∀ xs : List Bool, xs.length=n →
      ∃ P : Nat, 0<P ∧ Even P ∧ evolution P xs=xs := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro xs hn
      by_cases hz : xs=[]
      · subst xs
        exact ⟨2,by decide,by decide,rfl⟩
      have hpos : 0<xs.length := List.length_pos_iff.mpr hz
      obtain ⟨u,v,rfl⟩ := split_last xs hpos
      have hlen : u.length<n := by simp only [List.length_append,List.length_cons,List.length_nil] at hn;omega
      obtain ⟨P,hP,_,hr⟩ := ih u.length hlen u rfl
      exact ⟨2*P,by omega,⟨P,by omega⟩,extension_double_return u v P hr⟩
  exact all xs.length xs rfl

noncomputable def evenClock (xs : List Bool) : Nat := Nat.find (exists_even_whole_return xs)

theorem evenClock_spec (xs : List Bool) :
    0<evenClock xs ∧ Even (evenClock xs) ∧ evolution (evenClock xs) xs=xs :=
  Nat.find_spec (exists_even_whole_return xs)

theorem evenClock_le (xs : List Bool) (P : Nat)
    (hp : 0<P) (he : Even P) (hr : evolution P xs=xs) : evenClock xs≤P :=
  Nat.find_min' (exists_even_whole_return xs) ⟨hp,he,hr⟩

theorem prefix_return (u : List Bool) (v : Bool) (P : Nat)
    (hr : evolution P (u++[v])=u++[v]) : evolution P u=u := by
  rw [evolution_snoc] at hr
  exact ((snoc_eq _ _ _ _).mp hr).1

theorem prefix_clock_le (u : List Bool) (v : Bool) : evenClock u≤evenClock (u++[v]) := by
  obtain ⟨hp,he,hr⟩ := evenClock_spec (u++[v])
  exact evenClock_le u _ hp he (prefix_return u v _ hr)

theorem safe_last_clock_equal (u : List Bool) (v : Bool)
    (hs : CedarSafety.Safe (u++[v])) : evenClock (u++[v])=evenClock u := by
  apply Nat.le_antisymm
  · obtain ⟨hp,he,hr⟩ := evenClock_spec u
    exact evenClock_le _ _ hp he (safe_extension_preserves_even_return u v _ he hr hs)
  · exact prefix_clock_le u v

theorem clock_jump_intrinsic_entry (u : List Bool) (c d : Bool)
    (hs : CedarSafety.Safe ((u++[c])++[d]))
    (h8 : evolution 8 ((u++[c])++[d])≠(u++[c])++[d])
    (hj : evenClock u<evenClock ((u++[c])++[d])) :
    SpanTwo (tr u) ∧ evolution 8 u≠u := by
  obtain ⟨hp,he,hr⟩ := evenClock_spec u
  apply safe_clock_jump_entry u c d (evenClock u) he hr ?_ hs h8
  intro hfull
  have hl := evenClock_le ((u++[c])++[d]) _ hp he hfull
  omega

/-- Uniform, with no supplied period/anti-period hypothesis. Either the
two-cell actual ancestor enters the height-two/nonreturn problem, or the
entire Safe word has the exact SAME least even whole-return clock. -/
theorem safe_height_two_or_clock_plateau (u : List Bool) (c d : Bool)
    (hs : CedarSafety.Safe ((u++[c])++[d]))
    (h8 : evolution 8 ((u++[c])++[d])≠(u++[c])++[d]) :
    (SpanTwo (tr u) ∧ evolution 8 u≠u) ∨
      evenClock ((u++[c])++[d])=evenClock u := by
  have hle : evenClock u≤evenClock ((u++[c])++[d]) :=
    (prefix_clock_le u c).trans (prefix_clock_le (u++[c]) d)
  rcases Nat.eq_or_lt_of_le hle with he | hj
  · exact Or.inr he.symm
  · exact Or.inl (clock_jump_intrinsic_entry u c d hs h8 hj)

end SafeClockDichotomy
