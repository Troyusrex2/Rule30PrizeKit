import RootShortExtensionCore
import Mathlib.Tactic.FinCases

/-! Split exact trajectory witnesses for the short-extension lemma.
Every step is proved by ordinary kernel reduction; the generator is not trusted. -/
namespace RootShortExtensionCertificate
open CedarSafetySoundness CedarSafety RootShortExtensionCore
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option Elab.async false

def previous (i : Fin 28) : Nat → Bool := lift8 (state i).previous
def older (i : Fin 28) : Nat → Bool := lift8 (state i).older
def ShortOutcome (p r : Nat → Bool) (xs : List Bool) : Prop :=
  driven p r 8 xs=xs ∨ ∃ t : Nat,
    (driven p r t xs).getLastD (p t)=false ∧
    (driven p r (t+1) xs).getLastD (p (t+1))=false

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


theorem case_1_0 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_1 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_2 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_3 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_4 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_5 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_6 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_7 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨7,by decide⟩) = [false,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨7,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨7,by decide⟩) = [false,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨7,by decide⟩) = [true,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_8 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_9 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_10 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_11 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_12 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_13 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_1_14 : ShortOutcome (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 3 (shortWord ⟨14,by decide⟩) = [false,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 4 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 5 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 6 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 7 (shortWord ⟨14,by decide⟩) = [false,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨1,by decide⟩) (older ⟨1,by decide⟩) 8 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_0 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_1 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_2 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_3 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_4 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_5 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_6 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_7 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨7,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨7,by decide⟩) = [false,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨7,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨7,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨7,by decide⟩) = [true,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_8 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_9 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [false,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_10 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [false,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_11 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_12 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_13 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_2_14 : ShortOutcome (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 3 (shortWord ⟨14,by decide⟩) = [false,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 4 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 5 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 6 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 7 (shortWord ⟨14,by decide⟩) = [false,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨2,by decide⟩) (older ⟨2,by decide⟩) 8 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_0 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_1 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_2 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_3 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_4 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_5 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_6 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_7 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨7,by decide⟩) = [false,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨7,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨7,by decide⟩) = [false,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨7,by decide⟩) = [true,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_8 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_9 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_10 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_11 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [false,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_12 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [false,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_13 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_3_14 : ShortOutcome (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 3 (shortWord ⟨14,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 4 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 5 (shortWord ⟨14,by decide⟩) = [false,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 6 (shortWord ⟨14,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 7 (shortWord ⟨14,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨3,by decide⟩) (older ⟨3,by decide⟩) 8 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_0 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_1 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_2 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_3 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_4 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_5 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_6 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_7 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨7,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨7,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨7,by decide⟩) = [false,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨7,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨7,by decide⟩) = [true,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_8 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨8,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨8,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_9 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_10 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [false,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [false,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_11 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_12 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [false,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [false,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_13 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_4_14 : ShortOutcome (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 3 (shortWord ⟨14,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 4 (shortWord ⟨14,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 5 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 6 (shortWord ⟨14,by decide⟩) = [false,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 7 (shortWord ⟨14,by decide⟩) = [false,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨4,by decide⟩) (older ⟨4,by decide⟩) 8 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_0 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_1 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_2 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_3 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_4 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_5 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_6 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_7 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨7,by decide⟩) = [false,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨7,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨7,by decide⟩) = [false,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨7,by decide⟩) = [true,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_8 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_9 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_10 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_11 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [false,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_12 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [false,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_13 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_5_14 : ShortOutcome (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 3 (shortWord ⟨14,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 4 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 5 (shortWord ⟨14,by decide⟩) = [false,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 6 (shortWord ⟨14,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 7 (shortWord ⟨14,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨5,by decide⟩) (older ⟨5,by decide⟩) 8 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_0 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_1 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_2 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_3 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_4 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_5 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_6 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_7 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨7,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨7,by decide⟩) = [false,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨7,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨7,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨7,by decide⟩) = [true,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_8 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_9 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [false,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_10 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [false,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_11 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_12 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_13 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_6_14 : ShortOutcome (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 3 (shortWord ⟨14,by decide⟩) = [false,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 4 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 5 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 6 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 7 (shortWord ⟨14,by decide⟩) = [false,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨6,by decide⟩) (older ⟨6,by decide⟩) 8 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_0 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_1 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_2 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_3 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_4 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_5 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_6 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_7 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨7,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨7,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨7,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨7,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨7,by decide⟩) = [true,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_8 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨8,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨8,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_9 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [false,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [false,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_10 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [true,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_11 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [false,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [false,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_12 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_13 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨13,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨13,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_7_14 : ShortOutcome (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 3 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 4 (shortWord ⟨14,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 5 (shortWord ⟨14,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 6 (shortWord ⟨14,by decide⟩) = [false,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 7 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨7,by decide⟩) (older ⟨7,by decide⟩) 8 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_20_0 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_20_1 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 8 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 9 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 10 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 11 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 12 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h11]
    rfl
  refine Or.inr ⟨11,?_,?_⟩
  · rw [h11]; rfl
  · rw [h12]; rfl

theorem case_20_2 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  refine Or.inr ⟨3,?_,?_⟩
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem case_20_3 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 5 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 6 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 7 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 8 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  refine Or.inr ⟨7,?_,?_⟩
  · rw [h7]; rfl
  · rw [h8]; rfl

theorem case_20_4 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  refine Or.inr ⟨5,?_,?_⟩
  · rw [h5]; rfl
  · rw [h6]; rfl

theorem case_20_5 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 7 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 8 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 9 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 10 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 11 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 12 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 13 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 14 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h13]
    rfl
  refine Or.inr ⟨13,?_,?_⟩
  · rw [h13]; rfl
  · rw [h14]; rfl

theorem case_20_6 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  refine Or.inr ⟨3,?_,?_⟩
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem case_20_7 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_20_8 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  refine Or.inr ⟨2,?_,?_⟩
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem case_20_9 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [false,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 9 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 10 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h9]
    rfl
  refine Or.inr ⟨9,?_,?_⟩
  · rw [h9]; rfl
  · rw [h10]; rfl

theorem case_20_10 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  refine Or.inr ⟨5,?_,?_⟩
  · rw [h5]; rfl
  · rw [h6]; rfl

theorem case_20_11 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 8 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 9 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 10 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 11 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 12 (shortWord ⟨11,by decide⟩) = [true,true,false] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 13 (shortWord ⟨11,by decide⟩) = [false,false,true] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 14 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 15 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h14]
    rfl
  have h16 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 16 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h15]
    rfl
  have h17 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 17 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h16]
    rfl
  have h18 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 18 (shortWord ⟨11,by decide⟩) = [true,true,false] := by
    rw [driven,h17]
    rfl
  refine Or.inr ⟨17,?_,?_⟩
  · rw [h17]; rfl
  · rw [h18]; rfl

theorem case_20_12 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 9 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 10 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 11 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 12 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 13 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 14 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h13]
    rfl
  refine Or.inr ⟨13,?_,?_⟩
  · rw [h13]; rfl
  · rw [h14]; rfl

theorem case_20_13 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  refine Or.inr ⟨3,?_,?_⟩
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem case_20_14 : ShortOutcome (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨20,by decide⟩) (older ⟨20,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  refine Or.inr ⟨1,?_,?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl

theorem case_21_0 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_21_1 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 8 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 9 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 10 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 11 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 12 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 13 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 14 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 15 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h14]
    rfl
  have h16 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 16 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h15]
    rfl
  refine Or.inr ⟨15,?_,?_⟩
  · rw [h15]; rfl
  · rw [h16]; rfl

theorem case_21_2 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  refine Or.inr ⟨7,?_,?_⟩
  · rw [h7]; rfl
  · rw [h8]; rfl

theorem case_21_3 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 4 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 5 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 6 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 7 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 8 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 9 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 10 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 11 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 12 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h11]
    rfl
  refine Or.inr ⟨11,?_,?_⟩
  · rw [h11]; rfl
  · rw [h12]; rfl

theorem case_21_4 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 7 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 8 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 9 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 10 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h9]
    rfl
  refine Or.inr ⟨9,?_,?_⟩
  · rw [h9]; rfl
  · rw [h10]; rfl

theorem case_21_5 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  refine Or.inr ⟨3,?_,?_⟩
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem case_21_6 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  refine Or.inr ⟨1,?_,?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl

theorem case_21_7 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_21_8 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  refine Or.inr ⟨2,?_,?_⟩
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem case_21_9 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 9 (shortWord ⟨9,by decide⟩) = [false,false,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 10 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 11 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 12 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 13 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 14 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h13]
    rfl
  refine Or.inr ⟨13,?_,?_⟩
  · rw [h13]; rfl
  · rw [h14]; rfl

theorem case_21_10 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 9 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 10 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h9]
    rfl
  refine Or.inr ⟨9,?_,?_⟩
  · rw [h9]; rfl
  · rw [h10]; rfl

theorem case_21_11 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [false,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 8 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 9 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 10 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 11 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 12 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 13 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 14 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 15 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h14]
    rfl
  have h16 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 16 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h15]
    rfl
  have h17 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 17 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h16]
    rfl
  have h18 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 18 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h17]
    rfl
  refine Or.inr ⟨17,?_,?_⟩
  · rw [h17]; rfl
  · rw [h18]; rfl

theorem case_21_12 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  refine Or.inr ⟨3,?_,?_⟩
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem case_21_13 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 6 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h5]
    rfl
  refine Or.inr ⟨5,?_,?_⟩
  · rw [h5]; rfl
  · rw [h6]; rfl

theorem case_21_14 : ShortOutcome (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨21,by decide⟩) (older ⟨21,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  refine Or.inr ⟨1,?_,?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl

theorem case_22_0 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_22_1 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 8 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 9 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 10 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 11 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 12 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 13 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 14 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h13]
    rfl
  refine Or.inr ⟨13,?_,?_⟩
  · rw [h13]; rfl
  · rw [h14]; rfl

theorem case_22_2 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  refine Or.inr ⟨5,?_,?_⟩
  · rw [h5]; rfl
  · rw [h6]; rfl

theorem case_22_3 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 4 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 5 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 6 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 7 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 8 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 9 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 10 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h9]
    rfl
  refine Or.inr ⟨9,?_,?_⟩
  · rw [h9]; rfl
  · rw [h10]; rfl

theorem case_22_4 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 7 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 8 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  refine Or.inr ⟨7,?_,?_⟩
  · rw [h7]; rfl
  · rw [h8]; rfl

theorem case_22_5 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h5]
    rfl
  refine Or.inr ⟨5,?_,?_⟩
  · rw [h5]; rfl
  · rw [h6]; rfl

theorem case_22_6 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  refine Or.inr ⟨1,?_,?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl

theorem case_22_7 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_22_8 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  refine Or.inr ⟨2,?_,?_⟩
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem case_22_9 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [false,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 9 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 10 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 11 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 12 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h11]
    rfl
  refine Or.inr ⟨11,?_,?_⟩
  · rw [h11]; rfl
  · rw [h12]; rfl

theorem case_22_10 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  refine Or.inr ⟨7,?_,?_⟩
  · rw [h7]; rfl
  · rw [h8]; rfl

theorem case_22_11 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [false,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h5]
    rfl
  refine Or.inr ⟨5,?_,?_⟩
  · rw [h5]; rfl
  · rw [h6]; rfl

theorem case_22_12 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  refine Or.inr ⟨3,?_,?_⟩
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem case_22_13 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 6 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 7 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 8 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 9 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 10 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 11 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 12 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 13 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 14 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 15 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h14]
    rfl
  have h16 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 16 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h15]
    rfl
  refine Or.inr ⟨15,?_,?_⟩
  · rw [h15]; rfl
  · rw [h16]; rfl

theorem case_22_14 : ShortOutcome (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨22,by decide⟩) (older ⟨22,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  refine Or.inr ⟨1,?_,?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl

theorem case_23_0 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_23_1 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 8 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 9 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 10 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h9]
    rfl
  refine Or.inr ⟨9,?_,?_⟩
  · rw [h9]; rfl
  · rw [h10]; rfl

theorem case_23_2 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  refine Or.inr ⟨1,?_,?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl

theorem case_23_3 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 4 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 5 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 6 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  refine Or.inr ⟨5,?_,?_⟩
  · rw [h5]; rfl
  · rw [h6]; rfl

theorem case_23_4 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  refine Or.inr ⟨3,?_,?_⟩
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem case_23_5 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 7 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 8 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 9 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 10 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 11 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 12 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h11]
    rfl
  refine Or.inr ⟨11,?_,?_⟩
  · rw [h11]; rfl
  · rw [h12]; rfl

theorem case_23_6 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  refine Or.inr ⟨1,?_,?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl

theorem case_23_7 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_23_8 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 4 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 5 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 6 (shortWord ⟨8,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 7 (shortWord ⟨8,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 8 (shortWord ⟨8,by decide⟩) = [true,false,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 9 (shortWord ⟨8,by decide⟩) = [false,true,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 10 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 11 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 12 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 13 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 14 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 15 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h14]
    rfl
  have h16 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 16 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h15]
    rfl
  have h17 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 17 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h16]
    rfl
  have h18 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 18 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h17]
    rfl
  have h19 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 19 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h18]
    rfl
  have h20 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 20 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h19]
    rfl
  refine Or.inr ⟨19,?_,?_⟩
  · rw [h19]; rfl
  · rw [h20]; rfl

theorem case_23_9 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [false,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h7]
    rfl
  refine Or.inr ⟨7,?_,?_⟩
  · rw [h7]; rfl
  · rw [h8]; rfl

theorem case_23_10 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  refine Or.inr ⟨3,?_,?_⟩
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem case_23_11 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 8 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 9 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 10 (shortWord ⟨11,by decide⟩) = [true,true,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 11 (shortWord ⟨11,by decide⟩) = [false,false,true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 12 (shortWord ⟨11,by decide⟩) = [true,false,true] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 13 (shortWord ⟨11,by decide⟩) = [false,true,false] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 14 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 15 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h14]
    rfl
  have h16 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 16 (shortWord ⟨11,by decide⟩) = [true,true,false] := by
    rw [driven,h15]
    rfl
  refine Or.inr ⟨15,?_,?_⟩
  · rw [h15]; rfl
  · rw [h16]; rfl

theorem case_23_12 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [false,true,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 9 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 10 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 11 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 12 (shortWord ⟨12,by decide⟩) = [true,false,false] := by
    rw [driven,h11]
    rfl
  refine Or.inr ⟨11,?_,?_⟩
  · rw [h11]; rfl
  · rw [h12]; rfl

theorem case_23_13 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h4]
    rfl
  refine Or.inr ⟨4,?_,?_⟩
  · rw [h4]; rfl
  · rw [h5]; rfl

theorem case_23_14 : ShortOutcome (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨23,by decide⟩) (older ⟨23,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  refine Or.inr ⟨1,?_,?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl

theorem case_24_0 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_24_1 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  refine Or.inr ⟨2,?_,?_⟩
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem case_24_2 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 9 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 10 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 11 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h10]
    rfl
  refine Or.inr ⟨10,?_,?_⟩
  · rw [h10]; rfl
  · rw [h11]; rfl

theorem case_24_3 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  refine Or.inr ⟨2,?_,?_⟩
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem case_24_4 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 7 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 8 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 9 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 10 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 11 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 12 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 13 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h12]
    rfl
  refine Or.inr ⟨12,?_,?_⟩
  · rw [h12]; rfl
  · rw [h13]; rfl

theorem case_24_5 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  refine Or.inr ⟨4,?_,?_⟩
  · rw [h4]; rfl
  · rw [h5]; rfl

theorem case_24_6 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 5 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 6 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 7 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  refine Or.inr ⟨6,?_,?_⟩
  · rw [h6]; rfl
  · rw [h7]; rfl

theorem case_24_7 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_24_8 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  refine Or.inr ⟨2,?_,?_⟩
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem case_24_9 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 9 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 10 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 11 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 12 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 13 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h12]
    rfl
  refine Or.inr ⟨12,?_,?_⟩
  · rw [h12]; rfl
  · rw [h13]; rfl

theorem case_24_10 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 9 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 10 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 11 (shortWord ⟨10,by decide⟩) = [true,true,false] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 12 (shortWord ⟨10,by decide⟩) = [false,false,true] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 13 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 14 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 15 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h14]
    rfl
  have h16 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 16 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h15]
    rfl
  have h17 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 17 (shortWord ⟨10,by decide⟩) = [true,true,false] := by
    rw [driven,h16]
    rfl
  refine Or.inr ⟨16,?_,?_⟩
  · rw [h16]; rfl
  · rw [h17]; rfl

theorem case_24_11 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  refine Or.inr ⟨4,?_,?_⟩
  · rw [h4]; rfl
  · rw [h5]; rfl

theorem case_24_12 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [false,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 9 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h8]
    rfl
  refine Or.inr ⟨8,?_,?_⟩
  · rw [h8]; rfl
  · rw [h9]; rfl

theorem case_24_13 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 6 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 7 (shortWord ⟨13,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 8 (shortWord ⟨13,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 9 (shortWord ⟨13,by decide⟩) = [true,false,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 10 (shortWord ⟨13,by decide⟩) = [false,true,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 11 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 12 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 13 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 14 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 15 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h14]
    rfl
  have h16 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 16 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h15]
    rfl
  have h17 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 17 (shortWord ⟨13,by decide⟩) = [false,true,true] := by
    rw [driven,h16]
    rfl
  have h18 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 18 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h17]
    rfl
  have h19 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 19 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h18]
    rfl
  have h20 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 20 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h19]
    rfl
  have h21 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 21 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h20]
    rfl
  refine Or.inr ⟨20,?_,?_⟩
  · rw [h20]; rfl
  · rw [h21]; rfl

theorem case_24_14 : ShortOutcome (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨24,by decide⟩) (older ⟨24,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  refine Or.inr ⟨1,?_,?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl

theorem case_25_0 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_25_1 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 6 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 7 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h6]
    rfl
  refine Or.inr ⟨6,?_,?_⟩
  · rw [h6]; rfl
  · rw [h7]; rfl

theorem case_25_2 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 9 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 10 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 11 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 12 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 13 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 14 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 15 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h14]
    rfl
  refine Or.inr ⟨14,?_,?_⟩
  · rw [h14]; rfl
  · rw [h15]; rfl

theorem case_25_3 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_25_4 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  refine Or.inr ⟨2,?_,?_⟩
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem case_25_5 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 7 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 8 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 9 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h8]
    rfl
  refine Or.inr ⟨8,?_,?_⟩
  · rw [h8]; rfl
  · rw [h9]; rfl

theorem case_25_6 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 5 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 6 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 7 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 8 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 9 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 10 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 11 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h10]
    rfl
  refine Or.inr ⟨10,?_,?_⟩
  · rw [h10]; rfl
  · rw [h11]; rfl

theorem case_25_7 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_25_8 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 4 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 5 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h4]
    rfl
  refine Or.inr ⟨4,?_,?_⟩
  · rw [h4]; rfl
  · rw [h5]; rfl

theorem case_25_9 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  refine Or.inr ⟨2,?_,?_⟩
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem case_25_10 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [false,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 9 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 10 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 11 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 12 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 13 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 14 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 15 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h14]
    rfl
  have h16 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 16 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h15]
    rfl
  have h17 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 17 (shortWord ⟨10,by decide⟩) = [true,false,false] := by
    rw [driven,h16]
    rfl
  refine Or.inr ⟨16,?_,?_⟩
  · rw [h16]; rfl
  · rw [h17]; rfl

theorem case_25_11 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 8 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 9 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h8]
    rfl
  refine Or.inr ⟨8,?_,?_⟩
  · rw [h8]; rfl
  · rw [h9]; rfl

theorem case_25_12 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [false,false,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 9 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 10 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 11 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 12 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 13 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h12]
    rfl
  refine Or.inr ⟨12,?_,?_⟩
  · rw [h12]; rfl
  · rw [h13]; rfl

theorem case_25_13 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  refine Or.inr ⟨3,?_,?_⟩
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem case_25_14 : ShortOutcome (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨25,by decide⟩) (older ⟨25,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  refine Or.inr ⟨1,?_,?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl

theorem case_26_0 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_26_1 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_26_2 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 9 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h8]
    rfl
  refine Or.inr ⟨8,?_,?_⟩
  · rw [h8]; rfl
  · rw [h9]; rfl

theorem case_26_3 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_26_4 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 6 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 7 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 8 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 9 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 10 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 11 (shortWord ⟨4,by decide⟩) = [true,false] := by
    rw [driven,h10]
    rfl
  refine Or.inr ⟨10,?_,?_⟩
  · rw [h10]; rfl
  · rw [h11]; rfl

theorem case_26_5 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h2]
    rfl
  refine Or.inr ⟨2,?_,?_⟩
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem case_26_6 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 5 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  refine Or.inr ⟨4,?_,?_⟩
  · rw [h4]; rfl
  · rw [h5]; rfl

theorem case_26_7 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_26_8 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 4 (shortWord ⟨8,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  refine Or.inr ⟨3,?_,?_⟩
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem case_26_9 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 4 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 5 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 6 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 7 (shortWord ⟨9,by decide⟩) = [false,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 8 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 9 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 10 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 11 (shortWord ⟨9,by decide⟩) = [true,false,false] := by
    rw [driven,h10]
    rfl
  refine Or.inr ⟨10,?_,?_⟩
  · rw [h10]; rfl
  · rw [h11]; rfl

theorem case_26_10 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 6 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 7 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 8 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 9 (shortWord ⟨10,by decide⟩) = [true,true,false] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 10 (shortWord ⟨10,by decide⟩) = [false,false,true] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 11 (shortWord ⟨10,by decide⟩) = [true,false,true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 12 (shortWord ⟨10,by decide⟩) = [false,true,false] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 13 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 14 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 15 (shortWord ⟨10,by decide⟩) = [true,true,false] := by
    rw [driven,h14]
    rfl
  refine Or.inr ⟨14,?_,?_⟩
  · rw [h14]; rfl
  · rw [h15]; rfl

theorem case_26_11 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h2]
    rfl
  refine Or.inr ⟨2,?_,?_⟩
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem case_26_12 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [false,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h6]
    rfl
  refine Or.inr ⟨6,?_,?_⟩
  · rw [h6]; rfl
  · rw [h7]; rfl

theorem case_26_13 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 5 (shortWord ⟨13,by decide⟩) = [true,false,false] := by
    rw [driven,h4]
    rfl
  refine Or.inr ⟨4,?_,?_⟩
  · rw [h4]; rfl
  · rw [h5]; rfl

theorem case_26_14 : ShortOutcome (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [false,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 3 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 4 (shortWord ⟨14,by decide⟩) = [false,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 5 (shortWord ⟨14,by decide⟩) = [true,false,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 6 (shortWord ⟨14,by decide⟩) = [false,true,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 7 (shortWord ⟨14,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 8 (shortWord ⟨14,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 9 (shortWord ⟨14,by decide⟩) = [false,true,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 10 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 11 (shortWord ⟨14,by decide⟩) = [false,true,true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 12 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 13 (shortWord ⟨14,by decide⟩) = [false,true,true] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 14 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 15 (shortWord ⟨14,by decide⟩) = [false,true,true] := by
    rw [driven,h14]
    rfl
  have h16 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 16 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h15]
    rfl
  have h17 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 17 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rw [driven,h16]
    rfl
  have h18 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 18 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h17]
    rfl
  have h19 : driven (previous ⟨26,by decide⟩) (older ⟨26,by decide⟩) 19 (shortWord ⟨14,by decide⟩) = [true,false,false] := by
    rw [driven,h18]
    rfl
  refine Or.inr ⟨18,?_,?_⟩
  · rw [h18]; rfl
  · rw [h19]; rfl

theorem case_27_0 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨0,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨0,by decide⟩) = [] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 4 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 5 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 6 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 7 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 8 (shortWord ⟨0,by decide⟩) = [] := by
    rw [driven,h7]
    rfl
  exact Or.inl h8

theorem case_27_1 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨1,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨1,by decide⟩) = [false] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨1,by decide⟩) = [true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 4 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 5 (shortWord ⟨1,by decide⟩) = [false] := by
    rw [driven,h4]
    rfl
  refine Or.inr ⟨4,?_,?_⟩
  · rw [h4]; rfl
  · rw [h5]; rfl

theorem case_27_2 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨2,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨2,by decide⟩) = [true] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 4 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 5 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 6 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 7 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 8 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 9 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 10 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 11 (shortWord ⟨2,by decide⟩) = [true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 12 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 13 (shortWord ⟨2,by decide⟩) = [false] := by
    rw [driven,h12]
    rfl
  refine Or.inr ⟨12,?_,?_⟩
  · rw [h12]; rfl
  · rw [h13]; rfl

theorem case_27_3 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨3,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨3,by decide⟩) = [false,false] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨3,by decide⟩) = [true,false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_27_4 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨4,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨4,by decide⟩) = [false,true] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨4,by decide⟩) = [true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 4 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 5 (shortWord ⟨4,by decide⟩) = [false,false] := by
    rw [driven,h4]
    rfl
  refine Or.inr ⟨4,?_,?_⟩
  · rw [h4]; rfl
  · rw [h5]; rfl

theorem case_27_5 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨5,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨5,by decide⟩) = [false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 4 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 5 (shortWord ⟨5,by decide⟩) = [true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 6 (shortWord ⟨5,by decide⟩) = [false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 7 (shortWord ⟨5,by decide⟩) = [true,false] := by
    rw [driven,h6]
    rfl
  refine Or.inr ⟨6,?_,?_⟩
  · rw [h6]; rfl
  · rw [h7]; rfl

theorem case_27_6 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨6,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 4 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 5 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 6 (shortWord ⟨6,by decide⟩) = [false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 7 (shortWord ⟨6,by decide⟩) = [true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 8 (shortWord ⟨6,by decide⟩) = [false,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 9 (shortWord ⟨6,by decide⟩) = [true,false] := by
    rw [driven,h8]
    rfl
  refine Or.inr ⟨8,?_,?_⟩
  · rw [h8]; rfl
  · rw [h9]; rfl

theorem case_27_7 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨7,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨7,by decide⟩) = [false,false,false] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨7,by decide⟩) = [true,false,false] := by
    rw [driven,h0]
    rfl
  refine Or.inr ⟨0,?_,?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem case_27_8 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨8,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨8,by decide⟩) = [false,false,true] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨8,by decide⟩) = [true,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨8,by decide⟩) = [false,true,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨8,by decide⟩) = [true,false,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 4 (shortWord ⟨8,by decide⟩) = [false,true,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 5 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 6 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 7 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 8 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 9 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 10 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 11 (shortWord ⟨8,by decide⟩) = [false,true,true] := by
    rw [driven,h10]
    rfl
  have h12 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 12 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h11]
    rfl
  have h13 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 13 (shortWord ⟨8,by decide⟩) = [true,true,true] := by
    rw [driven,h12]
    rfl
  have h14 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 14 (shortWord ⟨8,by decide⟩) = [false,false,false] := by
    rw [driven,h13]
    rfl
  have h15 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 15 (shortWord ⟨8,by decide⟩) = [true,false,false] := by
    rw [driven,h14]
    rfl
  refine Or.inr ⟨14,?_,?_⟩
  · rw [h14]; rfl
  · rw [h15]; rfl

theorem case_27_9 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨9,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨9,by decide⟩) = [false,true,false] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨9,by decide⟩) = [true,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨9,by decide⟩) = [false,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨9,by decide⟩) = [true,true,false] := by
    rw [driven,h2]
    rfl
  refine Or.inr ⟨2,?_,?_⟩
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem case_27_10 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨10,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨10,by decide⟩) = [false,true,true] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨10,by decide⟩) = [true,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨10,by decide⟩) = [false,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨10,by decide⟩) = [true,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 4 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 5 (shortWord ⟨10,by decide⟩) = [false,false,false] := by
    rw [driven,h4]
    rfl
  refine Or.inr ⟨4,?_,?_⟩
  · rw [h4]; rfl
  · rw [h5]; rfl

theorem case_27_11 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨11,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨11,by decide⟩) = [false,true,true] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 4 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 5 (shortWord ⟨11,by decide⟩) = [true,true,true] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 6 (shortWord ⟨11,by decide⟩) = [false,false,false] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 7 (shortWord ⟨11,by decide⟩) = [true,false,false] := by
    rw [driven,h6]
    rfl
  refine Or.inr ⟨6,?_,?_⟩
  · rw [h6]; rfl
  · rw [h7]; rfl

theorem case_27_12 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨12,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 4 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h3]
    rfl
  have h5 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 5 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h4]
    rfl
  have h6 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 6 (shortWord ⟨12,by decide⟩) = [false,false,true] := by
    rw [driven,h5]
    rfl
  have h7 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 7 (shortWord ⟨12,by decide⟩) = [true,false,true] := by
    rw [driven,h6]
    rfl
  have h8 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 8 (shortWord ⟨12,by decide⟩) = [false,true,false] := by
    rw [driven,h7]
    rfl
  have h9 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 9 (shortWord ⟨12,by decide⟩) = [true,true,true] := by
    rw [driven,h8]
    rfl
  have h10 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 10 (shortWord ⟨12,by decide⟩) = [false,false,false] := by
    rw [driven,h9]
    rfl
  have h11 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 11 (shortWord ⟨12,by decide⟩) = [true,true,false] := by
    rw [driven,h10]
    rfl
  refine Or.inr ⟨10,?_,?_⟩
  · rw [h10]; rfl
  · rw [h11]; rfl

theorem case_27_13 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨13,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨13,by decide⟩) = [false,false,true] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨13,by decide⟩) = [true,true,true] := by
    rw [driven,h1]
    rfl
  have h3 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 3 (shortWord ⟨13,by decide⟩) = [false,false,false] := by
    rw [driven,h2]
    rfl
  have h4 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 4 (shortWord ⟨13,by decide⟩) = [true,true,false] := by
    rw [driven,h3]
    rfl
  refine Or.inr ⟨3,?_,?_⟩
  · rw [h3]; rfl
  · rw [h4]; rfl

theorem case_27_14 : ShortOutcome (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) (shortWord ⟨14,by decide⟩) := by
  have h0 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 0 (shortWord ⟨14,by decide⟩) = [true,true,true] := by
    rfl
  have h1 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 1 (shortWord ⟨14,by decide⟩) = [false,false,false] := by
    rw [driven,h0]
    rfl
  have h2 : driven (previous ⟨27,by decide⟩) (older ⟨27,by decide⟩) 2 (shortWord ⟨14,by decide⟩) = [true,true,false] := by
    rw [driven,h1]
    rfl
  refine Or.inr ⟨1,?_,?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl

theorem extension_certificate (i : Fin 28) (k : Fin 15)
    (ha : accepted (state i).q=true) : ShortOutcome (previous i) (older i) (shortWord k) := by
  fin_cases i
  · cases ha
  · fin_cases k
    · exact case_1_0
    · exact case_1_1
    · exact case_1_2
    · exact case_1_3
    · exact case_1_4
    · exact case_1_5
    · exact case_1_6
    · exact case_1_7
    · exact case_1_8
    · exact case_1_9
    · exact case_1_10
    · exact case_1_11
    · exact case_1_12
    · exact case_1_13
    · exact case_1_14
  · fin_cases k
    · exact case_2_0
    · exact case_2_1
    · exact case_2_2
    · exact case_2_3
    · exact case_2_4
    · exact case_2_5
    · exact case_2_6
    · exact case_2_7
    · exact case_2_8
    · exact case_2_9
    · exact case_2_10
    · exact case_2_11
    · exact case_2_12
    · exact case_2_13
    · exact case_2_14
  · fin_cases k
    · exact case_3_0
    · exact case_3_1
    · exact case_3_2
    · exact case_3_3
    · exact case_3_4
    · exact case_3_5
    · exact case_3_6
    · exact case_3_7
    · exact case_3_8
    · exact case_3_9
    · exact case_3_10
    · exact case_3_11
    · exact case_3_12
    · exact case_3_13
    · exact case_3_14
  · fin_cases k
    · exact case_4_0
    · exact case_4_1
    · exact case_4_2
    · exact case_4_3
    · exact case_4_4
    · exact case_4_5
    · exact case_4_6
    · exact case_4_7
    · exact case_4_8
    · exact case_4_9
    · exact case_4_10
    · exact case_4_11
    · exact case_4_12
    · exact case_4_13
    · exact case_4_14
  · fin_cases k
    · exact case_5_0
    · exact case_5_1
    · exact case_5_2
    · exact case_5_3
    · exact case_5_4
    · exact case_5_5
    · exact case_5_6
    · exact case_5_7
    · exact case_5_8
    · exact case_5_9
    · exact case_5_10
    · exact case_5_11
    · exact case_5_12
    · exact case_5_13
    · exact case_5_14
  · fin_cases k
    · exact case_6_0
    · exact case_6_1
    · exact case_6_2
    · exact case_6_3
    · exact case_6_4
    · exact case_6_5
    · exact case_6_6
    · exact case_6_7
    · exact case_6_8
    · exact case_6_9
    · exact case_6_10
    · exact case_6_11
    · exact case_6_12
    · exact case_6_13
    · exact case_6_14
  · fin_cases k
    · exact case_7_0
    · exact case_7_1
    · exact case_7_2
    · exact case_7_3
    · exact case_7_4
    · exact case_7_5
    · exact case_7_6
    · exact case_7_7
    · exact case_7_8
    · exact case_7_9
    · exact case_7_10
    · exact case_7_11
    · exact case_7_12
    · exact case_7_13
    · exact case_7_14
  · cases ha
  · cases ha
  · cases ha
  · cases ha
  · cases ha
  · cases ha
  · cases ha
  · cases ha
  · cases ha
  · cases ha
  · cases ha
  · cases ha
  · fin_cases k
    · exact case_20_0
    · exact case_20_1
    · exact case_20_2
    · exact case_20_3
    · exact case_20_4
    · exact case_20_5
    · exact case_20_6
    · exact case_20_7
    · exact case_20_8
    · exact case_20_9
    · exact case_20_10
    · exact case_20_11
    · exact case_20_12
    · exact case_20_13
    · exact case_20_14
  · fin_cases k
    · exact case_21_0
    · exact case_21_1
    · exact case_21_2
    · exact case_21_3
    · exact case_21_4
    · exact case_21_5
    · exact case_21_6
    · exact case_21_7
    · exact case_21_8
    · exact case_21_9
    · exact case_21_10
    · exact case_21_11
    · exact case_21_12
    · exact case_21_13
    · exact case_21_14
  · fin_cases k
    · exact case_22_0
    · exact case_22_1
    · exact case_22_2
    · exact case_22_3
    · exact case_22_4
    · exact case_22_5
    · exact case_22_6
    · exact case_22_7
    · exact case_22_8
    · exact case_22_9
    · exact case_22_10
    · exact case_22_11
    · exact case_22_12
    · exact case_22_13
    · exact case_22_14
  · fin_cases k
    · exact case_23_0
    · exact case_23_1
    · exact case_23_2
    · exact case_23_3
    · exact case_23_4
    · exact case_23_5
    · exact case_23_6
    · exact case_23_7
    · exact case_23_8
    · exact case_23_9
    · exact case_23_10
    · exact case_23_11
    · exact case_23_12
    · exact case_23_13
    · exact case_23_14
  · fin_cases k
    · exact case_24_0
    · exact case_24_1
    · exact case_24_2
    · exact case_24_3
    · exact case_24_4
    · exact case_24_5
    · exact case_24_6
    · exact case_24_7
    · exact case_24_8
    · exact case_24_9
    · exact case_24_10
    · exact case_24_11
    · exact case_24_12
    · exact case_24_13
    · exact case_24_14
  · fin_cases k
    · exact case_25_0
    · exact case_25_1
    · exact case_25_2
    · exact case_25_3
    · exact case_25_4
    · exact case_25_5
    · exact case_25_6
    · exact case_25_7
    · exact case_25_8
    · exact case_25_9
    · exact case_25_10
    · exact case_25_11
    · exact case_25_12
    · exact case_25_13
    · exact case_25_14
  · fin_cases k
    · exact case_26_0
    · exact case_26_1
    · exact case_26_2
    · exact case_26_3
    · exact case_26_4
    · exact case_26_5
    · exact case_26_6
    · exact case_26_7
    · exact case_26_8
    · exact case_26_9
    · exact case_26_10
    · exact case_26_11
    · exact case_26_12
    · exact case_26_13
    · exact case_26_14
  · fin_cases k
    · exact case_27_0
    · exact case_27_1
    · exact case_27_2
    · exact case_27_3
    · exact case_27_4
    · exact case_27_5
    · exact case_27_6
    · exact case_27_7
    · exact case_27_8
    · exact case_27_9
    · exact case_27_10
    · exact case_27_11
    · exact case_27_12
    · exact case_27_13
    · exact case_27_14

end RootShortExtensionCertificate
