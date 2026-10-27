module
public import Rule30PhysicalDefectBudgetResearch

/-! A literal 2P-shift mismatch in physical column one cannot remain true
for 2P+1 consecutive readings when the physical center is P-periodic.
This controls actual mismatch residence, including signed cancellations;
it does not bound the number of mismatch episodes or prove Problem 1. -/
@[expose] public section
namespace Rule30PhysicalDefectEpisodeResearch
open Rule30PhysicalDefectBudgetResearch Ruliology.CellularAutomata Rule30Jen

theorem xor_same_left (c a b : Bool) : xor (xor c a) (xor c b)=xor a b := by
  cases c <;> cases a <;> cases b <;> rfl

theorem or_of_live_defect (r z ro zo : Bool)
    (h0 : xor r ro=true) (h1 : xor (r || z) (ro || zo)=true) : (r || z)=r := by
  cases r <;> cases z <;> cases ro <;> cases zo <;> simp_all

/-- On an uninterrupted physical mismatch, the right bit is toggled only
by the shared center bit. The two histories are the same history Q apart. -/
theorem live_mismatch_step {T Q : Nat}
    (hc : ∀ s, T≤s → cell (s+Q) 0=cell s 0)
    (t : Nat) (ht : T+Q≤t)
    (h0 : mismatch Q t=true) (h1 : mismatch Q (t+1)=true) :
    cell (t+1) 1=xor (cell t 0) (cell t 1) := by
  have hs := periodic_mismatch_step hc t ht
  rw [h1] at hs
  change true=xor ((!cell t 2) && xor (cell t 1) (cell (t-Q) 1))
    ((!cell (t-Q) 1) && xor (cell t 2) (cell (t-Q) 2)) at hs
  rw [← or_difference] at hs
  have hh := or_of_live_defect (cell t 1) (cell t 2) (cell (t-Q) 1) (cell (t-Q) 2) h0 hs.symm
  change xor (cell t 0) (cell t 1 || cell t 2)=xor (cell t 0) (cell t 1)
  rw [hh]

/-- Two identical finite blocks of XOR drivers cancel. No infinite period
or whole-state return is supplied for x. -/
theorem xor_two_blocks (x c : Nat → Bool) (P t : Nat)
    (hc : ∀ j, j<P → c (t+P+j)=c (t+j))
    (hx : ∀ j, j<2*P → x (t+j+1)=xor (c (t+j)) (x (t+j))) :
    x (t+2*P)=x t := by
  have hd : ∀ j, j≤P → xor (x (t+P+j)) (x (t+j))=xor (x (t+P)) (x t) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro hj
        rw [show t+P+(j+1)=t+(P+j)+1 by omega,
          show t+(j+1)=t+j+1 by omega, hx (P+j) (by omega), hx j (by omega),
          show t+(P+j)=t+P+j by omega, hc j (by omega), xor_same_left]
        exact ih (by omega)
  have h := hd P (by omega)
  rw [show t+P+P=t+2*P by omega] at h
  have cancel (a b d : Bool) (hh : xor a b=xor b d) : a=d := by
    cases a <;> cases b <;> cases d <;> simp_all
  exact cancel _ _ _ h

/-- Q=2P is chosen once. The Q+1 readings include BOTH endpoints.
Every uninterrupted true mismatch episode after T+Q therefore has at
most Q readings; no common reset of physical column two is assumed. -/
theorem bounded_mismatch_episode {T P : Nat} (_hP : 0<P)
    (hc : ∀ s, T≤s → cell (s+P) 0=cell s 0)
    (t : Nat) (ht : T+2*P≤t) :
    ∃ j, j≤2*P ∧ mismatch (2*P) (t+j)=false := by
  apply Classical.byContradiction
  intro hn
  have hall : ∀ j, j≤2*P → mismatch (2*P) (t+j)=true := by
    intro j hj
    cases hh : mismatch (2*P) (t+j)
    · exact (hn ⟨j,hj,hh⟩).elim
    · rfl
  have hpq : P∣2*P := ⟨2,by omega⟩
  have hq := periodic_multiple hc hpq
  have hs : ∀ j, j<2*P → cell (t+j+1) 1=xor (cell (t+j) 0) (cell (t+j) 1) := by
    intro j hj
    apply live_mismatch_step hq (t+j) (by omega) (hall j (by omega))
    simpa only [Nat.add_assoc] using hall (j+1) (by omega)
  have he := xor_two_blocks (fun s => cell s 1) (fun s => cell s 0) P t
    (fun j _ => by
      have hh := hc (t+j) (by omega)
      simpa only [show t+j+P=t+P+j by omega] using hh) hs
  have hf := hall (2*P) (by omega)
  unfold mismatch at hf
  rw [show t+2*P-2*P=t by omega,he] at hf
  cases cell t 1 <;> simp_all

/-- The exact physical event whose frequency remains to be controlled. -/
theorem true_birth_iff {T Q : Nat}
    (hc : ∀ s, T≤s → cell (s+Q) 0=cell s 0)
    (t : Nat) (ht : T+Q≤t) :
    (mismatch Q t=false ∧ mismatch Q (t+1)=true) ↔
      (cell t 1=false ∧ cell (t-Q) 1=false ∧ cell t 2≠cell (t-Q) 2) := by
  rw [periodic_mismatch_step hc t ht]
  unfold mismatch persists forcing
  cases cell t 1 <;> cases cell (t-Q) 1 <;> cases cell t 2 <;> cases cell (t-Q) 2 <;> decide

end Rule30PhysicalDefectEpisodeResearch
