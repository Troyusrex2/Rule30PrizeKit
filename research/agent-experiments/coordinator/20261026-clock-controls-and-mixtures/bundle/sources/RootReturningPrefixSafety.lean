import RootShortExtensionCore

/-! Every Safe extension of at most three cells of a whole-word returning
prefix also returns after eight steps. The prefix need not itself be Safe.
The 36-pair certificate is followed by arbitrary-prefix induction. -/
namespace RootReturningPrefixSafety
open CedarSafetySoundness CedarSafety RootShortExtensionCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def shortWord (k : Fin 15) : List Bool :=
  match k.val with
  | 0 => []
  | 1 => [false]
  | 2 => [true]
  | 3 => [false,false]
  | 4 => [false,true]
  | 5 => [true,false]
  | 6 => [true,true]
  | 7 => [false,false,false]
  | 8 => [false,false,true]
  | 9 => [false,true,false]
  | 10 => [false,true,true]
  | 11 => [true,false,false]
  | 12 => [true,false,true]
  | 13 => [true,true,false]
  | 14 => [true,true,true]
  | _ => []

theorem shortWord_complete (xs : List Bool) (h : xs.length ≤ 3) :
    ∃ k : Fin 15, shortWord k = xs := by
  cases xs with
  | nil => decide
  | cons a xs =>
    cases xs with
    | nil => cases a <;> decide
    | cons b xs =>
      cases xs with
      | nil => cases a <;> cases b <;> decide
      | cons c xs =>
        cases xs with
        | nil => cases a <;> cases b <;> cases c <;> decide
        | cons d xs => simp only [List.length_cons] at h; omega

def witness (i : Fin 36) (k : Fin 15) : Nat :=
  let row := match i.val with
    | 0 => [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
    | 1 => [0,0,0,0,0,0,0,0,2,0,0,0,0,3,1]
    | 2 => [0,0,0,0,2,0,0,0,4,2,6,0,0,3,1]
    | 3 => [0,0,0,0,0,3,1,0,2,0,0,7,3,5,1]
    | 4 => [0,0,2,0,4,2,6,0,0,4,0,2,0,6,0]
    | 5 => [0,0,0,0,0,3,1,0,2,0,0,7,3,5,1]
    | 6 => [0,0,0,0,2,0,0,0,4,2,6,0,0,3,1]
    | 7 => [0,3,1,7,3,5,1,0,0,0,3,0,5,0,1]
    | 8 => [0,0,4,0,0,4,0,0,8,11,3,2,4,15,7]
    | 9 => [2,2,6,2,0,6,0,0,2,13,5,4,6,9,1]
    | 10 => [3,7,3,0,0,0,3,0,7,2,10,6,14,3,1]
    | 11 => [1,5,1,0,5,0,1,0,8,5,3,4,12,9,1]
    | 12 => [0,0,0,0,8,11,3,0,4,8,12,7,5,13,3]
    | 13 => [4,4,0,2,4,15,7,0,2,4,8,11,9,3,1]
    | 14 => [2,2,0,0,2,13,5,0,10,2,6,9,7,5,1]
    | 15 => [6,6,0,4,6,9,1,0,2,6,10,5,3,11,1]
    | 16 => [7,0,0,0,7,2,10,0,3,11,7,2,12,4,6]
    | 17 => [3,0,3,6,14,3,1,0,2,8,10,7,3,11,1]
    | 18 => [5,0,5,0,8,5,3,0,10,2,4,9,5,3,1]
    | 19 => [1,0,1,4,12,9,1,0,4,6,8,13,9,5,1]
    | 20 => [0,0,8,0,4,8,12,0,6,4,16,8,14,5,3]
    | 21 => [0,11,3,7,5,13,3,0,2,9,5,17,13,3,1]
    | 22 => [4,2,4,0,2,4,8,0,12,2,7,4,10,20,1]
    | 23 => [0,15,7,11,9,3,1,0,2,13,9,17,3,5,1]
    | 24 => [2,0,2,0,10,2,6,0,5,10,16,2,8,6,18]
    | 25 => [0,13,5,9,7,5,1,0,2,11,7,5,3,15,1]
    | 26 => [6,4,6,0,2,6,10,0,4,2,14,6,12,3,1]
    | 27 => [0,9,1,5,3,11,1,0,19,7,3,15,11,4,1]
    | 28 => [0,0,7,0,3,11,7,0,5,15,3,2,4,13,7]
    | 29 => [0,2,10,2,12,4,6,0,2,12,16,4,8,20,1]
    | 30 => [0,6,14,0,2,8,10,0,4,2,16,8,12,3,1]
    | 31 => [3,3,1,7,3,11,1,0,19,9,3,17,11,6,1]
    | 32 => [0,0,8,0,10,2,4,0,3,10,14,2,6,4,18]
    | 33 => [5,5,3,9,5,3,1,0,2,11,5,8,3,13,1]
    | 34 => [0,4,12,0,4,6,8,0,14,2,4,6,10,3,1]
    | 35 => [1,9,1,13,9,5,1,0,4,15,9,17,5,7,1]
    | _ => []
  row.getD k.val 0

def Case (i : Fin 36) (k : Fin 15) : Prop :=
  let p := lift8 (CedarSafetyBridge.state i).previous
  let r := lift8 (CedarSafetyBridge.state i).older
  let xs := shortWord k
  driven p r 8 xs=xs ∨
    ((driven p r (witness i k) xs).getLastD (p (witness i k))=false ∧
     (driven p r (witness i k+1) xs).getLastD (p (witness i k+1))=false)

instance (i : Fin 36) (k : Fin 15) : Decidable (Case i k) := by
  unfold Case
  infer_instance

theorem case_0 : ∀ k : Fin 15, Case ⟨0,by decide⟩ k := by decide +kernel
theorem case_1 : ∀ k : Fin 15, Case ⟨1,by decide⟩ k := by decide +kernel
theorem case_2 : ∀ k : Fin 15, Case ⟨2,by decide⟩ k := by decide +kernel
theorem case_3 : ∀ k : Fin 15, Case ⟨3,by decide⟩ k := by decide +kernel
theorem case_4 : ∀ k : Fin 15, Case ⟨4,by decide⟩ k := by decide +kernel
theorem case_5 : ∀ k : Fin 15, Case ⟨5,by decide⟩ k := by decide +kernel
theorem case_6 : ∀ k : Fin 15, Case ⟨6,by decide⟩ k := by decide +kernel
theorem case_7 : ∀ k : Fin 15, Case ⟨7,by decide⟩ k := by decide +kernel
theorem case_8 : ∀ k : Fin 15, Case ⟨8,by decide⟩ k := by decide +kernel
theorem case_9 : ∀ k : Fin 15, Case ⟨9,by decide⟩ k := by decide +kernel
theorem case_10 : ∀ k : Fin 15, Case ⟨10,by decide⟩ k := by decide +kernel
theorem case_11 : ∀ k : Fin 15, Case ⟨11,by decide⟩ k := by decide +kernel
theorem case_12 : ∀ k : Fin 15, Case ⟨12,by decide⟩ k := by decide +kernel
theorem case_13 : ∀ k : Fin 15, Case ⟨13,by decide⟩ k := by decide +kernel
theorem case_14 : ∀ k : Fin 15, Case ⟨14,by decide⟩ k := by decide +kernel
theorem case_15 : ∀ k : Fin 15, Case ⟨15,by decide⟩ k := by decide +kernel
theorem case_16 : ∀ k : Fin 15, Case ⟨16,by decide⟩ k := by decide +kernel
theorem case_17 : ∀ k : Fin 15, Case ⟨17,by decide⟩ k := by decide +kernel
theorem case_18 : ∀ k : Fin 15, Case ⟨18,by decide⟩ k := by decide +kernel
theorem case_19 : ∀ k : Fin 15, Case ⟨19,by decide⟩ k := by decide +kernel
theorem case_20 : ∀ k : Fin 15, Case ⟨20,by decide⟩ k := by decide +kernel
theorem case_21 : ∀ k : Fin 15, Case ⟨21,by decide⟩ k := by decide +kernel
theorem case_22 : ∀ k : Fin 15, Case ⟨22,by decide⟩ k := by decide +kernel
theorem case_23 : ∀ k : Fin 15, Case ⟨23,by decide⟩ k := by decide +kernel
theorem case_24 : ∀ k : Fin 15, Case ⟨24,by decide⟩ k := by decide +kernel
theorem case_25 : ∀ k : Fin 15, Case ⟨25,by decide⟩ k := by decide +kernel
theorem case_26 : ∀ k : Fin 15, Case ⟨26,by decide⟩ k := by decide +kernel
theorem case_27 : ∀ k : Fin 15, Case ⟨27,by decide⟩ k := by decide +kernel
theorem case_28 : ∀ k : Fin 15, Case ⟨28,by decide⟩ k := by decide +kernel
theorem case_29 : ∀ k : Fin 15, Case ⟨29,by decide⟩ k := by decide +kernel
theorem case_30 : ∀ k : Fin 15, Case ⟨30,by decide⟩ k := by decide +kernel
theorem case_31 : ∀ k : Fin 15, Case ⟨31,by decide⟩ k := by decide +kernel
theorem case_32 : ∀ k : Fin 15, Case ⟨32,by decide⟩ k := by decide +kernel
theorem case_33 : ∀ k : Fin 15, Case ⟨33,by decide⟩ k := by decide +kernel
theorem case_34 : ∀ k : Fin 15, Case ⟨34,by decide⟩ k := by decide +kernel
theorem case_35 : ∀ k : Fin 15, Case ⟨35,by decide⟩ k := by decide +kernel

theorem certificate (i : Fin 36) (k : Fin 15) : Case i k := by
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
  have h35 : i=35 := by omega
  subst i; exact case_35 k

theorem short_case_return (i : Fin 36) (xs : List Bool) (hv : xs.length≤3)
    (hs : DrivenSafe (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) xs) :
    driven (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) 8 xs=xs := by
  obtain ⟨k,rfl⟩ := shortWord_complete xs hv
  have hc := certificate i k
  unfold Case at hc
  rcases hc with hc | hc
  · exact hc
  · exact False.elim (hs (witness i k) hc)

theorem extension_aux (u : List Bool) : ∀ (i : Fin 36) (v : List Bool),
    v.length≤3 →
    run8 (CedarSafetyBridge.state i).previous (CedarSafetyBridge.state i).older u=u →
    DrivenSafe (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) (u++v) →
    driven (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) 8 (u++v)=u++v := by
  induction u with
  | nil => intro i v hv _ hs; exact short_case_return i v hv hs
  | cons a us ih =>
    intro i v hv hret hs
    rw [run8_cons,List.cons.injEq] at hret
    have hc := CedarSafetyBridge.transition_certificate i a
    simp only [hret.1,ite_true] at hc
    obtain ⟨j,_,hp,hr⟩ := hc
    have hs' := safe_cons (lift8 (CedarSafetyBridge.state i).previous)
      (lift8 (CedarSafetyBridge.state i).older) a (us++v) hs
    rw [history_lift8 _ _ _ hret.1] at hs'
    have sub := ih j v hv
    rw [hp,hr] at sub
    have ht := sub hret.2 hs'
    rw [List.cons_append,driven_cons,history_lift8 _ _ _ hret.1,ht]
    rfl

/-- Only the prefix's return is assumed. Safety belongs to the entire word. -/
theorem returning_prefix_safe_extension (u v : List Bool)
    (hu : evolution 8 u=u) (hv : v.length≤3) (hs : Safe (u++v)) :
    evolution 8 (u++v)=u++v := by
  have hu' : run8 zero zero u=u := by rwa [run8_white]
  have hs' := white_safe (u++v) hs
  have h := extension_aux u (0 : Fin 36) v hv
  change run8 zero zero u=u → DrivenSafe (lift8 zero) (lift8 zero) (u++v) →
    driven (lift8 zero) (lift8 zero) 8 (u++v)=u++v at h
  have hr := h hu' hs'
  rwa [driven_white] at hr

end RootReturningPrefixSafety
