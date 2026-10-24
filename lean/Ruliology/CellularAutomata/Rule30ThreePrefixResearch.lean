module

public import Ruliology.CellularAutomata.Rule30EtherThreeLeft

/-!
# A necessary first-defect condition for the period-three left constraint

There are two ether left halves with head phases (*,0,1) under the effective
010 boundary. A state satisfying the same constraint can first differ from
either reference only at a depth whose zero-based index is divisible by
three. This certifies the prefix-domain restriction used in ranking searches;
it does not prove a ranking or exclude a center-column period.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ThreePrefixResearch

open Rule30Jen Rule30DrivenLeft Rule30EtherThree

def offset (mode : Bool) : Nat := if mode then 11 else 2
def near (mode : Bool) : Nat := offset mode-1
def index (mode : Bool) (p : Int) : Nat := ((p+(offset mode:Int))%12).toNat
def reference (mode : Bool) (p : Int) : Bool := ether3 (index mode p) 0
def driver (t : Nat) : Bool := wordAt3 (effWord3 w011) t

theorem index_neg_one (mode : Bool) : index mode (-1)=near mode := by
  cases mode <;> decide

theorem boundary_table : ∀ mode : Bool, ∀ t : Fin 3,
    rule (ether3 (near mode+11) t.val) (ether3 (near mode) t.val) (driver t.val)=
      ether3 (near mode) (t.val+1) := by decide

theorem boundary_step (mode : Bool) (t : Nat) :
    rule (ether3 (near mode+11) t) (ether3 (near mode) t) (driver t)=
      ether3 (near mode) (t+1) := by
  have h := boundary_table mode ⟨t%3,Nat.mod_lt _ (by decide)⟩
  simpa [ether3,driver,wordAt3,effWord3_011,Nat.add_mod,Nat.mod_mod] using h

/-- Both references are actual evolutions under the same 010 boundary. -/
theorem reference_evolves (mode : Bool) : ∀ t p, p<0 →
    L driver (reference mode) t p=ether3 (index mode p) t := by
  intro t
  induction t with
  | zero => intro p hp; rw [L_zero hp]; rfl
  | succ t ih =>
      intro p hp
      rw [L_succ hp,ih (p-1) (by omega),ih p hp]
      have hl : ether3 (index mode (p-1)) t=ether3 (index mode p+11) t :=
        ether3_congr (by dsimp [index]; omega) rfl
      rw [hl]
      by_cases he : p = -1
      · subst p
        rw [show (-1:Int)+1=0 by rfl,L_col0,index_neg_one]
        exact boundary_step mode t
      · rw [ih (p+1) (by omega),ether3_rule]
        congr 1
        exact ether3_congr (by dsimp [index]; omega) rfl

theorem reference_fits_table : ∀ mode : Bool, ∀ t : Fin 3,
    fits3 (colPattern3 w011) t.val (ether3 (near mode) t.val)=true := by decide

theorem reference_fits (mode : Bool) (t : Nat) :
    fits3 (colPattern3 w011) (t%3) (L driver (reference mode) t (-1))=true := by
  rw [reference_evolves mode t (-1) (by omega),index_neg_one]
  have h := reference_fits_table mode ⟨t%3,Nat.mod_lt _ (by decide)⟩
  simpa only [ether3,Nat.mod_mod] using h

/-- Least-significant-bit-first data used by the independent prefix searches. -/
def baseBits (mode : Bool) : Nat := if mode then 159 else 1272

theorem reference_depth_table : ∀ mode : Bool, ∀ k : Fin 12,
    reference mode (-((k.val+1:Nat):Int))=(baseBits mode).testBit k.val := by decide

theorem reference_depth (mode : Bool) (k : Nat) :
    reference mode (-((k+1:Nat):Int))=(baseBits mode).testBit (k%12) := by
  have h := reference_depth_table mode ⟨k%12,Nat.mod_lt _ (by decide)⟩
  have he : index mode (-((k+1:Nat):Int))=index mode (-((k%12+1:Nat):Int)) := by
    dsimp [index]
    omega
  unfold reference
  rw [he]
  exact h

theorem reference_head (mode : Bool) : reference mode (-1)=mode := by
  cases mode <;> decide

def Constrained (s : Int → Bool) : Prop :=
  ∀ t, fits3 (colPattern3 w011) (t%3) (L driver s t (-1))=true

/-- The first differing cell is at depth d+1, with d counted from zero. -/
def FirstDefect (s : Int → Bool) (mode : Bool) (d : Nat) : Prop :=
  (∀ p : Int, -(d:Int)≤p → p<0 → s p=reference mode p) ∧
    s (-((d+1:Nat):Int))≠reference mode (-((d+1:Nat):Int))

theorem fits_unique_nonfree (t : Nat) (ht : t<3) (h0 : t≠0) (a b : Bool)
    (ha : fits3 (colPattern3 w011) t a=true)
    (hb : fits3 (colPattern3 w011) t b=true) : a=b := by
  rw [fits3_011] at ha hb
  have h : t=1 ∨ t=2 := by omega
  rcases h with rfl | rfl <;> cases a <;> cases b <;> simp_all

/-- A constrained row first differs from either reference only at a free phase. -/
theorem first_defect_multiple_three {s : Int → Bool} (hs : Constrained s)
    (mode : Bool) (d : Nat) (hd : FirstDefect s mode d) : d%3=0 := by
  apply Classical.byContradiction
  intro hphase
  have hflip : s (-((d+1:Nat):Int))= !reference mode (-((d+1:Nat):Int)) := by
    have hne := hd.2
    cases h1 : s (-((d+1:Nat):Int)) <;>
      cases h2 : reference mode (-((d+1:Nat):Int)) <;> simp_all
  have hp := permutive (c:=driver) hd.1 hflip
  have heq := fits_unique_nonfree (d%3) (Nat.mod_lt _ (by decide)) hphase
    (L driver s d (-1)) (L driver (reference mode) d (-1)) (hs d) (reference_fits mode d)
  rw [heq] at hp
  cases h : L driver (reference mode) d (-1) <;> simp_all

def LeftFinite (s : Int → Bool) : Prop :=
  ∃ M : Nat, ∀ p : Int, p < -(M:Int) → s p=false

private theorem least_bounded (P : Nat → Prop) : ∀ n,
    (∃ k, k≤n ∧ P k) → ∃ d, P d ∧ ∀ k, k<d → ¬P k := by
  classical
  intro n
  induction n with
  | zero =>
      rintro ⟨k,hk,hp⟩
      have he : k=0 := by omega
      subst k
      exact ⟨0,hp,fun k hk => by omega⟩
  | succ n ih =>
      intro hex
      by_cases hold : ∃ k, k≤n ∧ P k
      · exact ih hold
      · obtain ⟨k,hk,hp⟩ := hex
        have he : k=n+1 := by
          apply Classical.byContradiction
          intro hne
          exact hold ⟨k,by omega,hp⟩
        refine ⟨k,hp,fun j hj hpj => ?_⟩
        exact hold ⟨j,by omega,hpj⟩

/-- Every finite left row differs somewhere from either infinite reference. -/
theorem finite_first_defect {s : Int → Bool} (hf : LeftFinite s) (mode : Bool) :
    ∃ d, FirstDefect s mode d := by
  obtain ⟨M,hM⟩ := hf
  let n := 12*(M+1)+(if mode then 0 else 3)
  have hn : index mode (-((n+1:Nat):Int))=10 := by
    cases mode <;> dsimp [n,index,offset] <;> omega
  have hp : s (-((n+1:Nat):Int))≠reference mode (-((n+1:Nat):Int)) := by
    rw [hM _ (by cases mode <;> dsimp [n] <;> omega)]
    unfold reference
    rw [hn]
    decide
  obtain ⟨d,hd,hmin⟩ := least_bounded
    (fun k => s (-((k+1:Nat):Int))≠reference mode (-((k+1:Nat):Int))) n ⟨n,Nat.le_refl _,hp⟩
  refine ⟨d,?_,hd⟩
  intro p hp0 hp1
  let k := (-p).toNat-1
  have hk : k<d := by dsimp [k]; omega
  have he : p= -((k+1:Nat):Int) := by dsimp [k]; omega
  apply Classical.byContradiction
  intro hne
  exact hmin k hk (by simpa only [← he] using hne)

theorem finite_constrained_first_defect {s : Int → Bool}
    (hf : LeftFinite s) (hs : Constrained s) (mode : Bool) :
    ∃ d, FirstDefect s mode d ∧ d%3=0 := by
  obtain ⟨d,hd⟩ := finite_first_defect hf mode
  exact ⟨d,hd,first_defect_multiple_three hs mode d hd⟩

theorem driver_restart (n t : Nat) : driver (3*n+t)=driver t := by
  simp [driver,wordAt3,effWord3_011,Nat.add_mod]

/-- Restarting at a whole number of periods keeps the same boundary. -/
theorem restart_three (s : Int → Bool) (n : Nat) : ∀ t p, p≤0 →
    L driver (L driver s (3*n)) t p=L driver s (3*n+t) p := by
  intro t
  induction t with
  | zero =>
      intro p hp
      by_cases h : p<0
      · rw [L_zero h]; rfl
      · have he : p=0 := by omega
        subst p
        rw [L_col0,L_col0,driver_restart]
  | succ t ih =>
      intro p hp
      by_cases h : p<0
      · rw [show 3*n+(t+1)=(3*n+t)+1 by omega,L_succ h,L_succ h,
          ih (p-1) (by omega),ih p hp,ih (p+1) (by omega)]
      · have he : p=0 := by omega
        subst p
        rw [L_col0,L_col0,driver_restart]

theorem constrained_restart {s : Int → Bool} (hs : Constrained s) (n : Nat) :
    Constrained (L driver s (3*n)) := by
  intro t
  rw [restart_three s n t (-1) (by omega)]
  have h := hs (3*n+t)
  simpa only [Nat.add_mod,Nat.mul_mod,show 3%3=0 by decide,Nat.zero_mul,
    Nat.zero_add,Nat.mod_mod] using h

theorem finite_evolution (s : Int → Bool) (M : Nat)
    (hM : ∀ p : Int, p < -(M:Int) → s p=false) :
    ∀ t p, p < -((M+t:Nat):Int) → L driver s t p=false := by
  intro t
  induction t with
  | zero =>
      intro p hp
      rw [L_zero (by omega)]
      exact hM p (by omega)
  | succ t ih =>
      intro p hp
      rw [L_succ (by omega),ih (p-1) (by omega),ih p (by omega),ih (p+1) (by omega)]
      rfl

theorem leftFinite_evolution {s : Int → Bool} (hf : LeftFinite s) (t : Nat) :
    LeftFinite (L driver s t) := by
  obtain ⟨M,hM⟩ := hf
  exact ⟨M+t,finite_evolution s M hM t⟩

/-- The necessary domain restriction holds at every whole-period restart. -/
theorem every_cycle_first_defect {s : Int → Bool} (hf : LeftFinite s)
    (hs : Constrained s) (n : Nat) (mode : Bool) :
    ∃ d, FirstDefect (L driver s (3*n)) mode d ∧ d%3=0 :=
  finite_constrained_first_defect (leftFinite_evolution hf (3*n))
    (constrained_restart hs n) mode

end Ruliology.CellularAutomata.Rule30ThreePrefixResearch
