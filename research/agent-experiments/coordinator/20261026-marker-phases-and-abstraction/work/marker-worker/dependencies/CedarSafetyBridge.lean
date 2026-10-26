import CedarSafetySemantics

/-!
Exact limited language bridge: all-time newest safety AND full-word return
after eight genuine finite-white updates is equivalent to the old DFA.
The return hypothesis is explicit; this proves no safety completeness.
-/
namespace CedarSafetyBridge
open CedarSafetySoundness CedarSafety
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def state (i : Fin 36) : CertificateState :=
  match i.val with
  | 0 => ⟨0,ofNat 0,ofNat 0⟩
  | 1 => ⟨1,ofNat 511,ofNat 0⟩
  | 2 => ⟨2,ofNat 170,ofNat 511⟩
  | 3 => ⟨3,ofNat 341,ofNat 511⟩
  | 4 => ⟨4,ofNat 170,ofNat 170⟩
  | 5 => ⟨3,ofNat 341,ofNat 170⟩
  | 6 => ⟨2,ofNat 170,ofNat 341⟩
  | 7 => ⟨5,ofNat 341,ofNat 341⟩
  | 8 => ⟨6,ofNat 204,ofNat 170⟩
  | 9 => ⟨6,ofNat 307,ofNat 170⟩
  | 10 => ⟨7,ofNat 102,ofNat 341⟩
  | 11 => ⟨8,ofNat 409,ofNat 341⟩
  | 12 => ⟨9,ofNat 180,ofNat 204⟩
  | 13 => ⟨9,ofNat 331,ofNat 204⟩
  | 14 => ⟨9,ofNat 210,ofNat 307⟩
  | 15 => ⟨9,ofNat 301,ofNat 307⟩
  | 16 => ⟨9,ofNat 90,ofNat 102⟩
  | 17 => ⟨10,ofNat 421,ofNat 102⟩
  | 18 => ⟨10,ofNat 150,ofNat 409⟩
  | 19 => ⟨10,ofNat 361,ofNat 409⟩
  | 20 => ⟨11,ofNat 168,ofNat 180⟩
  | 21 => ⟨12,ofNat 343,ofNat 180⟩
  | 22 => ⟨11,ofNat 138,ofNat 331⟩
  | 23 => ⟨12,ofNat 373,ofNat 331⟩
  | 24 => ⟨11,ofNat 162,ofNat 210⟩
  | 25 => ⟨12,ofNat 349,ofNat 210⟩
  | 26 => ⟨11,ofNat 42,ofNat 301⟩
  | 27 => ⟨12,ofNat 469,ofNat 301⟩
  | 28 => ⟨11,ofNat 84,ofNat 90⟩
  | 29 => ⟨12,ofNat 427,ofNat 90⟩
  | 30 => ⟨12,ofNat 186,ofNat 421⟩
  | 31 => ⟨11,ofNat 325,ofNat 421⟩
  | 32 => ⟨12,ofNat 234,ofNat 150⟩
  | 33 => ⟨11,ofNat 277,ofNat 150⟩
  | 34 => ⟨12,ofNat 174,ofNat 361⟩
  | 35 => ⟨11,ofNat 337,ofNat 361⟩
  | _ => ⟨0,zero,zero⟩

theorem endpoint_certificate : ∀ i : Fin 36,
    accepted (state i).q = true ↔ ProfileSafe (state i).previous := by decide

theorem transition_certificate : ∀ (i : Fin 36) (v : Bool),
    if (nextProfile (state i).previous (state i).older v).t8 = v then
      ∃ j : Fin 36, (state j).q = transition (state i).q v ∧
        (state j).previous = nextProfile (state i).previous (state i).older v ∧
        (state j).older = (state i).previous
    else transition (state i).q v = 11 := by decide

/-- Spatial induction: a wrong older return cannot be repaired by later cells. -/
theorem bridge_aux (xs : List Bool) : ∀ i : Fin 36,
    accepted (read (state i).q xs) = true ↔
      run8 (state i).previous (state i).older xs = xs ∧
      ProfileSafe (profileTrace (state i).previous (state i).older xs) := by
  induction xs with
  | nil =>
    intro i
    simpa only [CedarSafetySoundness.read,run8_nil,profileTrace,true_and] using endpoint_certificate i
  | cons v vs ih =>
    intro i
    by_cases hret : (nextProfile (state i).previous (state i).older v).t8 = v
    · have cert := transition_certificate i v
      simp only [hret,ite_true] at cert
      obtain ⟨j,hq,hp,hr⟩ := cert
      have sub := ih j
      rw [hq,hp,hr] at sub
      simpa only [CedarSafetySoundness.read,run8_cons,hret,List.cons.injEq,true_and,profileTrace] using sub
    · have cert := transition_certificate i v
      simp only [hret,ite_false] at cert
      constructor
      · intro h
        change accepted (read (transition (state i).q v) vs) = true at h
        rw [cert,sink_read] at h
        contradiction
      · intro h
        have bad := congrArg List.head? h.1
        simp only [run8_cons,List.head?_cons,Option.some.injEq] at bad
        exact False.elim (hret bad)

theorem accepted_iff_return_window (xs : List Bool) :
    accepted (read 0 xs) = true ↔ evolution 8 xs = xs ∧ EightWindow xs := by
  have h := bridge_aux xs ⟨0,by decide⟩
  change accepted (read 0 xs) = true ↔ run8 zero zero xs = xs ∧
    ProfileSafe (profileTrace zero zero xs) at h
  rw [run8_white,profile_safe_iff_window] at h
  exact h

/-- All finite widths, including the correctly rejected empty word. -/
theorem safe_return_iff_accepted (xs : List Bool) :
    (Safe xs ∧ evolution 8 xs = xs) ↔ accepted (read 0 xs) = true := by
  constructor
  · rintro ⟨hs,hr⟩
    exact (accepted_iff_return_window xs).mpr ⟨hr,(safe_iff_window_of_return8 hr).mp hs⟩
  · intro h
    obtain ⟨hr,hw⟩ := (accepted_iff_return_window xs).mp h
    exact ⟨(safe_iff_window_of_return8 hr).mpr hw,hr⟩

/-- The two unproved global completeness targets are equivalent. Neither is assumed true. -/
theorem return_completeness_iff_language_completeness :
    (∀ xs, Safe xs → evolution 8 xs = xs) ↔
      (∀ xs, Safe xs → accepted (read 0 xs) = true) := by
  constructor
  · intro h xs hs
    exact (safe_return_iff_accepted xs).mp ⟨hs,h xs hs⟩
  · intro h xs hs
    exact ((safe_return_iff_accepted xs).mpr (h xs hs)).2

end CedarSafetyBridge
