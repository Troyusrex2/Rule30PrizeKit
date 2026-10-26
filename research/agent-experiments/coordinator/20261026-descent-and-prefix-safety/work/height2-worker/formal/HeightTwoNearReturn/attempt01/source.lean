import RootShortExtensionCore
import RootEventHeight

/-! A fixed finite certificate for at most two extensions of every return8
profile pair. The subsequent semantic induction is over arbitrary prefixes. -/
namespace HeightTwoNearReturn
open CedarSafetySoundness CedarSafety CedarSafetyBridge RootShortExtensionCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def whiteHeight (b : Nat → Bool) : Nat → Int
  | 0 => 0
  | t+1 => whiteHeight b t + RootEventHeight.sign t * RootEventHeight.white (b t)

def trace (p r : Nat → Bool) (xs : List Bool) (t : Nat) : Bool :=
  (driven p r t xs).getLastD (p t)

def SpanTwo (b : Nat → Bool) : Prop :=
  ∃ lo : Int, ∀ t, lo ≤ whiteHeight b t ∧ whiteHeight b t ≤ lo+2

def shortWord (k : Fin 7) : List Bool :=
  match k.val with
  | 0 => []
  | 1 => [false]
  | 2 => [true]
  | 3 => [false,false]
  | 4 => [false,true]
  | 5 => [true,false]
  | _ => [true,true]

def witness (i : Fin 36) (k : Fin 7) : Nat × Nat :=
  let row := match i.val with
    | 0 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 1 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 2 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 3 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 4 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 5 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 6 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 7 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 8 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 9 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 10 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 11 => [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
    | 12 => [(0,0), (0,0), (0,0), (7,0), (15,6), (3,12), (11,4)]
    | 13 => [(0,0), (0,0), (0,0), (3,10), (11,2), (7,0), (0,8)]
    | 14 => [(0,0), (0,0), (0,0), (1,8), (9,0), (5,14), (13,6)]
    | 15 => [(0,0), (0,0), (0,0), (5,0), (13,4), (1,10), (9,2)]
    | 16 => [(0,0), (0,0), (0,0), (1,6), (5,14), (3,10), (11,2)]
    | 17 => [(0,0), (0,0), (0,0), (7,0), (15,6), (1,10), (9,2)]
    | 18 => [(0,0), (0,0), (0,0), (1,8), (9,0), (3,12), (11,4)]
    | 19 => [(0,0), (0,0), (0,0), (5,12), (13,4), (7,0), (0,8)]
    | 20 => [(0,0), (7,0), (15,6), (1,16), (17,0), (9,0), (25,8)]
    | 21 => [(0,0), (3,12), (11,4), (11,28), (27,12), (3,20), (19,4)]
    | 22 => [(0,0), (3,10), (11,2), (13,0), (3,12), (5,20), (21,4)]
    | 23 => [(0,0), (7,0), (0,8), (15,0), (0,16), (7,24), (23,8)]
    | 24 => [(0,0), (1,8), (9,0), (1,10), (11,0), (3,18), (19,2)]
    | 25 => [(0,0), (5,14), (13,6), (13,30), (29,14), (21,6), (5,22)]
    | 26 => [(0,0), (5,0), (13,4), (1,14), (15,0), (7,22), (23,6)]
    | 27 => [(0,0), (1,10), (9,2), (9,26), (25,10), (1,18), (17,2)]
    | 28 => [(0,0), (1,6), (5,14), (15,0), (0,16), (7,24), (23,8)]
    | 29 => [(0,0), (3,10), (11,2), (3,18), (19,2), (11,26), (27,10)]
    | 30 => [(0,0), (7,0), (15,6), (7,22), (23,6), (15,0), (31,14)]
    | 31 => [(0,0), (1,10), (9,2), (3,20), (19,4), (1,12), (11,2)]
    | 32 => [(0,0), (1,8), (9,0), (1,16), (17,0), (9,24), (25,8)]
    | 33 => [(0,0), (3,12), (11,4), (5,22), (21,6), (13,0), (0,14)]
    | 34 => [(0,0), (5,12), (13,4), (21,4), (5,20), (13,28), (29,12)]
    | 35 => [(0,0), (7,0), (0,8), (9,0), (0,10), (1,18), (17,2)]
    | _ => []
  row.getD k.val (0,0)

def Case (i : Fin 36) (k : Fin 7) : Prop :=
  let p := lift8 (CedarSafetyBridge.state i).previous
  let r := lift8 (CedarSafetyBridge.state i).older
  let xs := shortWord k
  driven p r 8 xs = xs ∨
    2 < whiteHeight (trace p r xs) (witness i k).1 -
      whiteHeight (trace p r xs) (witness i k).2

instance (i : Fin 36) (k : Fin 7) : Decidable (Case i k) := by
  unfold Case
  infer_instance

theorem case_0 : ∀ k : Fin 7, Case ⟨0,by decide⟩ k := by decide +kernel
theorem case_1 : ∀ k : Fin 7, Case ⟨1,by decide⟩ k := by decide +kernel
theorem case_2 : ∀ k : Fin 7, Case ⟨2,by decide⟩ k := by decide +kernel
theorem case_3 : ∀ k : Fin 7, Case ⟨3,by decide⟩ k := by decide +kernel
theorem case_4 : ∀ k : Fin 7, Case ⟨4,by decide⟩ k := by decide +kernel
theorem case_5 : ∀ k : Fin 7, Case ⟨5,by decide⟩ k := by decide +kernel
theorem case_6 : ∀ k : Fin 7, Case ⟨6,by decide⟩ k := by decide +kernel
theorem case_7 : ∀ k : Fin 7, Case ⟨7,by decide⟩ k := by decide +kernel
theorem case_8 : ∀ k : Fin 7, Case ⟨8,by decide⟩ k := by decide +kernel
theorem case_9 : ∀ k : Fin 7, Case ⟨9,by decide⟩ k := by decide +kernel
theorem case_10 : ∀ k : Fin 7, Case ⟨10,by decide⟩ k := by decide +kernel
theorem case_11 : ∀ k : Fin 7, Case ⟨11,by decide⟩ k := by decide +kernel
theorem case_12 : ∀ k : Fin 7, Case ⟨12,by decide⟩ k := by decide +kernel
theorem case_13 : ∀ k : Fin 7, Case ⟨13,by decide⟩ k := by decide +kernel
theorem case_14 : ∀ k : Fin 7, Case ⟨14,by decide⟩ k := by decide +kernel
theorem case_15 : ∀ k : Fin 7, Case ⟨15,by decide⟩ k := by decide +kernel
theorem case_16 : ∀ k : Fin 7, Case ⟨16,by decide⟩ k := by decide +kernel
theorem case_17 : ∀ k : Fin 7, Case ⟨17,by decide⟩ k := by decide +kernel
theorem case_18 : ∀ k : Fin 7, Case ⟨18,by decide⟩ k := by decide +kernel
theorem case_19 : ∀ k : Fin 7, Case ⟨19,by decide⟩ k := by decide +kernel
theorem case_20 : ∀ k : Fin 7, Case ⟨20,by decide⟩ k := by decide +kernel
theorem case_21 : ∀ k : Fin 7, Case ⟨21,by decide⟩ k := by decide +kernel
theorem case_22 : ∀ k : Fin 7, Case ⟨22,by decide⟩ k := by decide +kernel
theorem case_23 : ∀ k : Fin 7, Case ⟨23,by decide⟩ k := by decide +kernel
theorem case_24 : ∀ k : Fin 7, Case ⟨24,by decide⟩ k := by decide +kernel
theorem case_25 : ∀ k : Fin 7, Case ⟨25,by decide⟩ k := by decide +kernel
theorem case_26 : ∀ k : Fin 7, Case ⟨26,by decide⟩ k := by decide +kernel
theorem case_27 : ∀ k : Fin 7, Case ⟨27,by decide⟩ k := by decide +kernel
theorem case_28 : ∀ k : Fin 7, Case ⟨28,by decide⟩ k := by decide +kernel
theorem case_29 : ∀ k : Fin 7, Case ⟨29,by decide⟩ k := by decide +kernel
theorem case_30 : ∀ k : Fin 7, Case ⟨30,by decide⟩ k := by decide +kernel
theorem case_31 : ∀ k : Fin 7, Case ⟨31,by decide⟩ k := by decide +kernel
theorem case_32 : ∀ k : Fin 7, Case ⟨32,by decide⟩ k := by decide +kernel
theorem case_33 : ∀ k : Fin 7, Case ⟨33,by decide⟩ k := by decide +kernel
theorem case_34 : ∀ k : Fin 7, Case ⟨34,by decide⟩ k := by decide +kernel
theorem case_35 : ∀ k : Fin 7, Case ⟨35,by decide⟩ k := by decide +kernel

theorem certificate (i : Fin 36) (k : Fin 7) : Case i k := by
  rcases i with ⟨i,hi⟩
  by_cases h0 : i = 0
  · subst i; exact case_0 k
  by_cases h1 : i = 1
  · subst i; exact case_1 k
  by_cases h2 : i = 2
  · subst i; exact case_2 k
  by_cases h3 : i = 3
  · subst i; exact case_3 k
  by_cases h4 : i = 4
  · subst i; exact case_4 k
  by_cases h5 : i = 5
  · subst i; exact case_5 k
  by_cases h6 : i = 6
  · subst i; exact case_6 k
  by_cases h7 : i = 7
  · subst i; exact case_7 k
  by_cases h8 : i = 8
  · subst i; exact case_8 k
  by_cases h9 : i = 9
  · subst i; exact case_9 k
  by_cases h10 : i = 10
  · subst i; exact case_10 k
  by_cases h11 : i = 11
  · subst i; exact case_11 k
  by_cases h12 : i = 12
  · subst i; exact case_12 k
  by_cases h13 : i = 13
  · subst i; exact case_13 k
  by_cases h14 : i = 14
  · subst i; exact case_14 k
  by_cases h15 : i = 15
  · subst i; exact case_15 k
  by_cases h16 : i = 16
  · subst i; exact case_16 k
  by_cases h17 : i = 17
  · subst i; exact case_17 k
  by_cases h18 : i = 18
  · subst i; exact case_18 k
  by_cases h19 : i = 19
  · subst i; exact case_19 k
  by_cases h20 : i = 20
  · subst i; exact case_20 k
  by_cases h21 : i = 21
  · subst i; exact case_21 k
  by_cases h22 : i = 22
  · subst i; exact case_22 k
  by_cases h23 : i = 23
  · subst i; exact case_23 k
  by_cases h24 : i = 24
  · subst i; exact case_24 k
  by_cases h25 : i = 25
  · subst i; exact case_25 k
  by_cases h26 : i = 26
  · subst i; exact case_26 k
  by_cases h27 : i = 27
  · subst i; exact case_27 k
  by_cases h28 : i = 28
  · subst i; exact case_28 k
  by_cases h29 : i = 29
  · subst i; exact case_29 k
  by_cases h30 : i = 30
  · subst i; exact case_30 k
  by_cases h31 : i = 31
  · subst i; exact case_31 k
  by_cases h32 : i = 32
  · subst i; exact case_32 k
  by_cases h33 : i = 33
  · subst i; exact case_33 k
  by_cases h34 : i = 34
  · subst i; exact case_34 k
  have : i = 35 := by omega
  subst i; exact case_35 k

theorem shortWord_complete (xs : List Bool) (h : xs.length ≤ 2) :
    ∃ k : Fin 7, xs = shortWord k := by
  cases xs with
  | nil => exact ⟨⟨0,by decide⟩,rfl⟩
  | cons a xs =>
    cases xs with
    | nil => cases a <;> first | exact ⟨⟨1,by decide⟩,rfl⟩ | exact ⟨⟨2,by decide⟩,rfl⟩
    | cons b xs =>
      cases xs with
      | nil => cases a <;> cases b <;>
          first | exact ⟨⟨3,by decide⟩,rfl⟩ | exact ⟨⟨4,by decide⟩,rfl⟩ |
            exact ⟨⟨5,by decide⟩,rfl⟩ | exact ⟨⟨6,by decide⟩,rfl⟩
      | cons c xs => simp only [List.length_cons] at h; omega

theorem whiteHeight_eq (b : Nat → Bool) (t : Nat) :
    whiteHeight b t = RootEventHeight.height (fun s => !b s) t := by
  induction t with
  | zero => exact (RootEventHeight.height_zero _).symm
  | succ t ih =>
    rw [whiteHeight,RootEventHeight.height_succ,ih]
    cases hb : b t <;> simp [RootEventHeight.white,RootEventHeight.bit,hb]

theorem trace_cons (p r : Nat → Bool) (a : Bool) (xs : List Bool) :
    trace p r (a::xs) = trace (history p r a) p xs := by
  funext t
  simp only [trace,driven_cons,List.getLastD_cons]

theorem short_case_return (i : Fin 36) (xs : List Bool) (hv : xs.length ≤ 2)
    (hh : SpanTwo (trace (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) xs)) :
    driven (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) 8 xs = xs := by
  obtain ⟨k,rfl⟩ := shortWord_complete xs hv
  have hc := certificate i k
  unfold Case at hc
  rcases hc with hc | hc
  · exact hc
  · obtain ⟨lo,hl⟩ := hh
    have hhi := hl (witness i k).1
    have hlo := hl (witness i k).2
    omega

theorem extension_aux (u : List Bool) : ∀ (i : Fin 36) (v : List Bool),
    v.length ≤ 2 →
    run8 (CedarSafetyBridge.state i).previous (CedarSafetyBridge.state i).older u = u →
    SpanTwo (trace (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) (u++v)) →
    driven (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) 8 (u++v) = u++v := by
  induction u with
  | nil => intro i v hv _ hh; exact short_case_return i v hv hh
  | cons a us ih =>
    intro i v hv hret hh
    rw [run8_cons,List.cons.injEq] at hret
    have hc := CedarSafetyBridge.transition_certificate i a
    simp only [hret.1,if_true] at hc
    obtain ⟨j,_,hp,hr⟩ := hc
    have hs := hh
    rw [List.cons_append,trace_cons,history_lift8 _ _ _ hret.1] at hs
    have sub := ih j v hv
    rw [hp,hr] at sub
    have ht := sub hret.2 hs
    rw [List.cons_append,driven_cons,history_lift8 _ _ _ hret.1,ht]
    rfl

/-- All widths and all time: a white-height band of width two cannot occur
at a nonreturning extension of at most two cells of an actual returning prefix.
Only the prefix has a supplied whole-word clock; the extension has none. -/
theorem height_two_short_extension (u v : List Bool) (hu : evolution 8 u = u)
    (hv : v.length ≤ 2)
    (hh : SpanTwo (fun t => newest (evolution t (u++v)))) :
    evolution 8 (u++v) = u++v := by
  have hs : SpanTwo (trace (lift8 zero) (lift8 zero) (u++v)) := by
    simpa only [trace,driven_white,lift8_zero,newest] using hh
  have hu' : run8 zero zero u = u := by rwa [run8_white]
  have h := extension_aux u ⟨0,by decide⟩ v hv hu' hs
  simpa only [CedarSafetyBridge.state,driven_white] using h

/-- A genuinely non-eight-periodic newest column in a height-two band has
no whole-word-return8 prefix within its two immediate spatial ancestors. -/
theorem no_near_return_prefix (u v : List Bool) (hv : v.length ≤ 2)
    (hh : SpanTwo (fun t => newest (evolution t (u++v))))
    (hn : ¬ ∀ t, newest (evolution (t+8) (u++v)) = newest (evolution t (u++v))) :
    evolution 8 u ≠ u := by
  intro hu
  have hr := height_two_short_extension u v hu hv hh
  exact hn (fun t => congrArg newest (return8_periodic hr t))

end HeightTwoNearReturn
