import CedarSafetyBridge
import Rule30ColumnReaderResearch

/-! Safety completeness discharges the safe-output half of the reader's sink
separation problem. It does not discharge unsafe equal traces or any fixed
physical-center observer. All assumptions remain explicit. -/
namespace PrizeSafetyBridge
open CedarSafetySoundness CedarSafety CedarSafetyBridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def stable : List (List Nat) := [[0,1],[2,3],[4,5],[6,7],[8,9],[6,7],[4,5],[10,11],[12,13],[14,15],[16,17],[18,19],[0,20],[0,21],[0,22],[0,23],[0,24],[25,0],[26,0],[27,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
def rtable : List (List Nat) := [[0,1,4,5,15,5,4,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[2,3,6,7,15,7,6,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[8,9,12,13,16,13,12,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[10,11,14,12,15,12,14,16,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,16,15,12,15,16,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[10,11,14,12,15,12,14,16,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[8,9,12,13,16,13,12,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,16,15,16,15,12,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,12]]
def snext (i : Fin 28) (a : Bool) : Fin 28 :=
  ⟨((stable.getD i.val []).getD (if a then 1 else 0) 0) % 28, Nat.mod_lt _ (by decide)⟩
def pairState (i j : Fin 28) : Nat := (rtable.getD i.val []).getD j.val 15

theorem single_certificate : ∀ (i : Fin 28) (a : Bool), transition (state i).q a ≠ 11 →
    (state (snext i a)).q = transition (state i).q a ∧
    (state (snext i a)).previous = nextProfile (state i).previous (state i).older a ∧
    (state (snext i a)).older = (state i).previous := by decide +kernel

def PairStep (i : Fin 28) : Prop := ∀ (j : Fin 28) (a b : Bool),
    transition (state i).q a ≠ 11 → transition (state j).q b ≠ 11 →
    Rule30ColumnReaderResearch.next (pairState i j) (a,b) = pairState (snext i a) (snext j b)
instance (i : Fin 28) : Decidable (PairStep i) := by unfold PairStep;infer_instance
theorem step_0 : PairStep ⟨0,by decide⟩ := by decide +kernel
theorem step_1 : PairStep ⟨1,by decide⟩ := by decide +kernel
theorem step_2 : PairStep ⟨2,by decide⟩ := by decide +kernel
theorem step_3 : PairStep ⟨3,by decide⟩ := by decide +kernel
theorem step_4 : PairStep ⟨4,by decide⟩ := by decide +kernel
theorem step_5 : PairStep ⟨5,by decide⟩ := by decide +kernel
theorem step_6 : PairStep ⟨6,by decide⟩ := by decide +kernel
theorem step_7 : PairStep ⟨7,by decide⟩ := by decide +kernel
theorem step_8 : PairStep ⟨8,by decide⟩ := by decide +kernel
theorem step_9 : PairStep ⟨9,by decide⟩ := by decide +kernel
theorem step_10 : PairStep ⟨10,by decide⟩ := by decide +kernel
theorem step_11 : PairStep ⟨11,by decide⟩ := by decide +kernel
theorem step_12 : PairStep ⟨12,by decide⟩ := by decide +kernel
theorem step_13 : PairStep ⟨13,by decide⟩ := by decide +kernel
theorem step_14 : PairStep ⟨14,by decide⟩ := by decide +kernel
theorem step_15 : PairStep ⟨15,by decide⟩ := by decide +kernel
theorem step_16 : PairStep ⟨16,by decide⟩ := by decide +kernel
theorem step_17 : PairStep ⟨17,by decide⟩ := by decide +kernel
theorem step_18 : PairStep ⟨18,by decide⟩ := by decide +kernel
theorem step_19 : PairStep ⟨19,by decide⟩ := by decide +kernel
theorem step_20 : PairStep ⟨20,by decide⟩ := by decide +kernel
theorem step_21 : PairStep ⟨21,by decide⟩ := by decide +kernel
theorem step_22 : PairStep ⟨22,by decide⟩ := by decide +kernel
theorem step_23 : PairStep ⟨23,by decide⟩ := by decide +kernel
theorem step_24 : PairStep ⟨24,by decide⟩ := by decide +kernel
theorem step_25 : PairStep ⟨25,by decide⟩ := by decide +kernel
theorem step_26 : PairStep ⟨26,by decide⟩ := by decide +kernel
theorem step_27 : PairStep ⟨27,by decide⟩ := by decide +kernel
theorem pair_step (i : Fin 28) : PairStep i := by
  have h : i.val < 28 := i.isLt
  match i with
  | ⟨0,_⟩ => exact step_0
  | ⟨1,_⟩ => exact step_1
  | ⟨2,_⟩ => exact step_2
  | ⟨3,_⟩ => exact step_3
  | ⟨4,_⟩ => exact step_4
  | ⟨5,_⟩ => exact step_5
  | ⟨6,_⟩ => exact step_6
  | ⟨7,_⟩ => exact step_7
  | ⟨8,_⟩ => exact step_8
  | ⟨9,_⟩ => exact step_9
  | ⟨10,_⟩ => exact step_10
  | ⟨11,_⟩ => exact step_11
  | ⟨12,_⟩ => exact step_12
  | ⟨13,_⟩ => exact step_13
  | ⟨14,_⟩ => exact step_14
  | ⟨15,_⟩ => exact step_15
  | ⟨16,_⟩ => exact step_16
  | ⟨17,_⟩ => exact step_17
  | ⟨18,_⟩ => exact step_18
  | ⟨19,_⟩ => exact step_19
  | ⟨20,_⟩ => exact step_20
  | ⟨21,_⟩ => exact step_21
  | ⟨22,_⟩ => exact step_22
  | ⟨23,_⟩ => exact step_23
  | ⟨24,_⟩ => exact step_24
  | ⟨25,_⟩ => exact step_25
  | ⟨26,_⟩ => exact step_26
  | ⟨27,_⟩ => exact step_27
  | ⟨n+28,h⟩ => omega

theorem output_certificate : ∀ (i j : Fin 28),
    accepted (state i).q = true → accepted (state j).q = true →
    (state i).previous = (state j).previous → Rule30ColumnReaderResearch.accepted (pairState i j) = true := by
  decide +kernel

theorem accepted_profiles (ss : List Rule30ColumnReaderResearch.Symbol) : ∀ i j : Fin 28,
    accepted (read (state i).q (ss.map Prod.fst)) = true →
    accepted (read (state j).q (ss.map Prod.snd)) = true →
    profileTrace (state i).previous (state i).older (ss.map Prod.fst) =
      profileTrace (state j).previous (state j).older (ss.map Prod.snd) →
    Rule30ColumnReaderResearch.accepted (Rule30ColumnReaderResearch.run (pairState i j) ss) = true := by
  induction ss with
  | nil => intro i j ha hb he; exact output_certificate i j ha hb he
  | cons s ss ih =>
      intro i j ha hb he
      have la : transition (state i).q s.1 ≠ 11 := by
        intro hz
        change accepted (read (transition (state i).q s.1) (ss.map Prod.fst)) = true at ha
        rw [hz,sink_read] at ha
        contradiction
      have lb : transition (state j).q s.2 ≠ 11 := by
        intro hz
        change accepted (read (transition (state j).q s.2) (ss.map Prod.snd)) = true at hb
        rw [hz,sink_read] at hb
        contradiction
      have ca := single_certificate i s.1 la
      have cb := single_certificate j s.2 lb
      have ha' : accepted (read (state (snext i s.1)).q (ss.map Prod.fst)) = true := by
        rw [ca.1];exact ha
      have hb' : accepted (read (state (snext j s.2)).q (ss.map Prod.snd)) = true := by
        rw [cb.1];exact hb
      have he' : profileTrace (state (snext i s.1)).previous (state (snext i s.1)).older (ss.map Prod.fst) =
          profileTrace (state (snext j s.2)).previous (state (snext j s.2)).older (ss.map Prod.snd) := by
        rw [ca.2.1,ca.2.2,cb.2.1,cb.2.2]
        exact he
      change Rule30ColumnReaderResearch.accepted (Rule30ColumnReaderResearch.run (Rule30ColumnReaderResearch.next (pairState i j) s) ss) = true
      rw [pair_step i j s.1 s.2 la lb]
      exact ih (snext i s.1) (snext j s.2) ha' hb' he'

theorem profile_ext (p q : Profile)
    (h : ∀ t : Fin 9, profileAt p t.val = profileAt q t.val) : p = q := by
  have h0 := h ⟨0,by decide⟩
  have h1 := h ⟨1,by decide⟩
  have h2 := h ⟨2,by decide⟩
  have h3 := h ⟨3,by decide⟩
  have h4 := h ⟨4,by decide⟩
  have h5 := h ⟨5,by decide⟩
  have h6 := h ⟨6,by decide⟩
  have h7 := h ⟨7,by decide⟩
  have h8 := h ⟨8,by decide⟩
  cases p;cases q;simp_all [profileAt]

theorem safe_language_equal_reader (ss : List Rule30ColumnReaderResearch.Symbol)
    (ha : accepted (read 0 (ss.map Prod.fst)) = true)
    (hb : accepted (read 0 (ss.map Prod.snd)) = true)
    (he : ∀ t : Fin 9, newest (evolution t.val (ss.map Prod.fst)) =
      newest (evolution t.val (ss.map Prod.snd))) :
    Rule30ColumnReaderResearch.accepted (Rule30ColumnReaderResearch.run 0 ss) = true := by
  have hp : profileTrace zero zero (ss.map Prod.fst) = profileTrace zero zero (ss.map Prod.snd) := by
    apply profile_ext
    intro t
    rw [trace_white _ t.val (by omega),trace_white _ t.val (by omega)]
    exact he t
  have hz : state (0 : Fin 28) = ⟨0,zero,zero⟩ := by decide +kernel
  have hr : pairState (0 : Fin 28) (0 : Fin 28) = 0 := by decide +kernel
  have h := accepted_profiles ss (0 : Fin 28) (0 : Fin 28)
  rw [hz,hr] at h
  exact h ha hb hp

/-- This is exactly the global Safe -> whole-word F^8 return premise. -/
def ReturnComplete : Prop := ∀ xs : List Bool, Safe xs → evolution 8 xs = xs

theorem safe_equal_reader (hr : ReturnComplete) (ss : List Rule30ColumnReaderResearch.Symbol)
    (ha : Safe (ss.map Prod.fst))
    (he : ∀ t, newest (evolution t (ss.map Prod.fst)) = newest (evolution t (ss.map Prod.snd))) :
    Rule30ColumnReaderResearch.accepted (Rule30ColumnReaderResearch.run 0 ss) = true := by
  have hb : Safe (ss.map Prod.snd) := by
    intro t hbad
    exact ha t ⟨(he t).trans hbad.1,(he (t+1)).trans hbad.2⟩
  apply safe_language_equal_reader ss
  · exact (safe_return_iff_accepted _).mp ⟨ha,hr _ ha⟩
  · exact (safe_return_iff_accepted _).mp ⟨hb,hr _ hb⟩
  · intro t;exact he t.val

theorem safe_sink_separates (hr : ReturnComplete) (ss : List Rule30ColumnReaderResearch.Symbol)
    (ha : Safe (ss.map Prod.fst)) (hs : Rule30ColumnReaderResearch.run 0 ss = 15) :
    ∃ t, newest (evolution t (ss.map Prod.fst)) ≠ newest (evolution t (ss.map Prod.snd)) := by
  apply Classical.byContradiction
  intro hn
  have he : ∀ t, newest (evolution t (ss.map Prod.fst)) = newest (evolution t (ss.map Prod.snd)) := by
    intro t
    apply Classical.byContradiction
    intro h
    exact hn ⟨t,h⟩
  have h := safe_equal_reader hr ss ha he
  rw [hs] at h
  contradiction

end PrizeSafetyBridge
