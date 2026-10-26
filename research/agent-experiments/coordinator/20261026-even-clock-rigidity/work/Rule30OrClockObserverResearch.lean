module
public import Rule30CommonPastResearch

/-! A uniform inverse lemma for OR traces at a clock-extending column.
If the newer profile flips after one driving period, the OR trace recovers
the older profile. A zero in that older profile and forced flips recover
the newer profile too. Non-clock-extending collisions are not resolved. -/
@[expose] public section
namespace Rule30OrClockObserverResearch
open Rule30CommonPastResearch
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem or_delta (x y e : Bool) :
    xor (x || y) ((xor x e) || y)=(!y && e) := by
  cases x <;> cases y <;> cases e <;> rfl
theorem xor_cancel_pair (x y e : Bool) :
    xor (xor x e) (xor y e)=xor x y := by
  cases x <;> cases y <;> cases e <;> rfl
theorem xor_recover (x y e : Bool) (h : xor x y=e) : x=xor y e := by
  cases x <;> cases y <;> cases e <;> simp_all
theorem masked_ne (x y h : Bool) (he : (x || h)=(y || h)) (hn : x≠y) : h=true := by
  cases x <;> cases y <;> cases h <;> simp_all
theorem flip_ne (x y : Bool) (h : x≠y) : xor x true≠xor y true := by
  cases x <;> cases y <;> simp_all

/-- A periodic xor driver gives a constant half-clock flip flag. -/
theorem shift_flag (g d : Nat → Bool) (P : Nat)
    (hs : ∀ t, g (t+1)=xor (g t) (d t))
    (hp : ∀ t, d (t+P)=d t) :
    ∀ t, g (t+P)=xor (g t) (xor (g P) (g 0)) := by
  have he : ∀ t, xor (g (t+P)) (g t)=xor (g P) (g 0) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show t+1+P=(t+P)+1 by omega,hs (t+P),hs t,hp t,xor_cancel_pair]
      exact ih
  exact fun t => xor_recover _ _ _ (he t)

/-- Taking a driving-period difference of the OR trace exposes the mask. -/
theorem older_recovered (g h g' h' : Nat → Bool) (P : Nat) (e : Bool)
    (hg : ∀ t, g (t+P)=xor (g t) true)
    (hh : ∀ t, h (t+P)=h t)
    (hg' : ∀ t, g' (t+P)=xor (g' t) e)
    (hh' : ∀ t, h' (t+P)=h' t)
    (ho : ∀ t, (g t || h t)=(g' t || h' t))
    (hz : ∃ s, h s=false) : e=true ∧ ∀ t, h t=h' t := by
  have hm : ∀ t, (!h t)=(!h' t && e) := by
    intro t
    have he : xor (g t || h t) (g (t+P) || h (t+P))=
        xor (g' t || h' t) (g' (t+P) || h' (t+P)) := by rw [ho t,ho (t+P)]
    rw [hg t,hh t,hg' t,hh' t,or_delta,or_delta] at he
    simpa only [Bool.and_true] using he
  have he : e=true := by
    obtain ⟨s,hs⟩ := hz
    have h := hm s
    cases e <;> simp_all
  refine ⟨he,?_⟩
  intro t
  have heq := hm t
  rw [he,Bool.and_true] at heq
  have hn := congrArg (fun x : Bool => !x) heq
  simpa only [Bool.not_not] using hn

/-- Differences hidden behind black masks persist forward; a periodic zero
forces them to be absent. No clock assumption on g or g' is used here. -/
theorem hidden_difference_impossible (g g' h : Nat → Bool) (P : Nat) (hP : 0<P)
    (hp : ∀ t, h (t+P)=h t) (hz : ∃ s, h s=false)
    (ho : ∀ t, (g t || h t)=(g' t || h t))
    (hs : ∀ t, h t=true → g (t+1)=xor (g t) true)
    (hs' : ∀ t, h t=true → g' (t+1)=xor (g' t) true) : ∀ t, g t=g' t := by
  intro t
  apply Classical.byContradiction
  intro hn
  have persist : ∀ n, g (t+n)≠g' (t+n) := by
    intro n
    induction n with
    | zero => simpa using hn
    | succ n ih =>
      have hb := masked_ne _ _ _ (ho (t+n)) ih
      rw [show t+(n+1)=(t+n)+1 by omega,hs _ hb,hs' _ hb]
      exact flip_ne _ _ ih
  have future : ∀ s, t≤s → h s=true := by
    intro s hst
    have h := persist (s-t)
    rw [show t+(s-t)=s by omega] at h
    exact masked_ne _ _ _ (ho s) h
  obtain ⟨s,hz⟩ := hz
  have hall := periodic_prop_retro (fun s => h s=true) P t hP
    (fun s => by rw [hp s]) future s
  rw [hz] at hall
  contradiction

theorem or_pair_injective_of_anti (g h g' h' : Nat → Bool) (P : Nat) (hP : 0<P) (e : Bool)
    (hg : ∀ t, g (t+P)=xor (g t) true)
    (hh : ∀ t, h (t+P)=h t)
    (hg' : ∀ t, g' (t+P)=xor (g' t) e)
    (hh' : ∀ t, h' (t+P)=h' t)
    (ho : ∀ t, (g t || h t)=(g' t || h' t))
    (hz : ∃ s, h s=false)
    (hs : ∀ t, h t=true → g (t+1)=xor (g t) true)
    (hs' : ∀ t, h' t=true → g' (t+1)=xor (g' t) true) :
    e=true ∧ (∀ t, h t=h' t) ∧ (∀ t, g t=g' t) := by
  obtain ⟨he,hhx⟩ := older_recovered g h g' h' P e hg hh hg' hh' ho hz
  refine ⟨he,hhx,?_⟩
  apply hidden_difference_impossible g g' h P hP hh hz
  · intro t;simpa only [hhx t] using ho t
  · exact hs
  · intro t ht;exact hs' t (by rw [←hhx t];exact ht)

/-- Actual Rule 30 profiles supply the other constant flip flag automatically. -/
theorem actual_or_clock_observer (a b : Nat → Nat → Bool) (ha : Actual a) (hb : Actual b)
    (j P : Nat) (hP : 0<P)
    (ap : ∀ t, a (t+P) (j+1)=a t (j+1))
    (bp : ∀ t, b (t+P) (j+1)=b t (j+1)) (bq : ∀ t, b (t+P) j=b t j)
    (anti : ∀ t, a (t+P) (j+2)=xor (a t (j+2)) true)
    (ho : ∀ t, (a t (j+2) || a t (j+1))=(b t (j+2) || b t (j+1)))
    (hz : ∃ s, a s (j+1)=false) :
    (∀ t, a t (j+1)=b t (j+1)) ∧ (∀ t, a t (j+2)=b t (j+2)) := by
  have bs : ∀ t, b (t+1) (j+2)=xor (b t (j+2)) (b t (j+1) || b t j) := fun t => hb t (j+2)
  have bper : ∀ t, (b (t+P) (j+1) || b (t+P) j)=(b t (j+1) || b t j) := by
    intro t;rw [bp t,bq t]
  have flag := shift_flag (fun t => b t (j+2)) (fun t => b t (j+1) || b t j) P bs bper
  have result := or_pair_injective_of_anti (fun t => a t (j+2)) (fun t => a t (j+1))
    (fun t => b t (j+2)) (fun t => b t (j+1)) P hP
    (xor (b P (j+2)) (b 0 (j+2))) anti ap flag bp ho hz
    (by intro t ht;rw [ha t (j+2)];simp [march,ht])
    (by intro t ht;rw [hb t (j+2)];simp [march,ht])
  exact result.2

/-! The plateau case cannot be obtained by keeping only two local Rule 30
equations and periodic upstream profiles. These bands do not assert a finite
white spatial ancestry. They refute a proposed weakening, not the observer. -/
def bandTable : List (List (List Bool)) := [
  [[false,true,false,true,false,true,true,true],
   [false,true,true,false,true,false,false,true],
   [true,false,false,true,true,false,false,true],
   [true,false,true,false,true,false,true,false]],
  [[false,false,true,true,false,true,false,true],
   [false,true,false,false,true,false,true,true],
   [false,true,false,true,false,true,false,true],
   [true,true,false,false,true,true,false,false]]]
def band (s j t : Nat) : Bool := ((bandTable.getD s []).getD j []).getD (t%8) false
def BandFacts (t : Nat) : Prop :=
  (band 0 0 t || band 0 1 t)=(band 1 0 t || band 1 1 t) ∧
  (∀ s∈[0,1], band s 1 (t+4)=xor (band s 1 t) true ∧
    band s 2 (t+4)=band s 2 t ∧ band s 3 (t+4)=band s 3 t ∧
    band s 0 (t+1)=xor (band s 0 t) (band s 1 t || band s 2 t) ∧
    band s 1 (t+1)=xor (band s 1 t) (band s 2 t || band s 3 t))
instance (t : Nat) : Decidable (BandFacts t) := by unfold BandFacts;infer_instance
theorem band_check : (List.range 8).all (fun t => decide (BandFacts t))=true := by decide +kernel
theorem band_facts (t : Nat) : BandFacts t := by
  have he := of_decide_eq_true (List.all_eq_true.mp band_check (t%8) (List.mem_range.mpr (Nat.mod_lt t (by decide))))
  simpa only [BandFacts,band,Nat.add_mod,Nat.mod_mod] using he
theorem band_periodic (s j t : Nat) : band s j (t+8)=band s j t := by
  simp only [band,Nat.add_mod,Nat.mod_mod,Nat.mod_self,Nat.add_zero]
theorem plateau_local_counterexample :
    (∀ t, BandFacts t) ∧
    (band 0 0 0 || band 0 1 0)=false ∧
    (band 1 0 0 || band 1 1 0)=false ∧ band 0 0 1≠band 1 0 1 := by
  exact ⟨band_facts,by decide,by decide,by decide⟩

end Rule30OrClockObserverResearch
