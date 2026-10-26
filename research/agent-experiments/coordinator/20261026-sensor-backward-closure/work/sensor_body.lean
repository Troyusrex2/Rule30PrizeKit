/-! All equations use physical positions. No hypothesis about a backward
common-field constraint is needed for the nonlifting conclusion. -/

theorem prefix_agreement (U E H t : Nat)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (he : 2*H+1 ≤ E) (ht : t ≤ H)
    (p : Int) (hp : (U : Int)-t-1 ≤ p) :
    cell (U+t) p=evol (unit U) t p := by
  rw [← restart]
  apply evol_local
  intro q hq _
  apply hgap
  omega

theorem pulse_mode (U V E H t : Nat)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (he : 2*H+1 ≤ E) (hUV : V+2*H+3 ≤ U) (ht : t ≤ H) :
    (∀ p, diffStep (cell (U+t)) (cell (V+t)) (evol (unit U) t) p =
      evol (unit U) (t+1) p) ∧
    Common (cell (U+t)) (cell (V+t)) (evol (unit U) t) := by
  apply local_mode
  intro p hb
  have hp : (U : Int)-t-1 ≤ p := by
    rcases hb with hb | hb
    · have := pulse_support U t p hb; omega
    · have := pulse_support U t (p+1) hb; omega
  refine ⟨prefix_agreement U E H t hgap he ht p hp,
    prefix_agreement U E H t hgap he ht (p+1) (by omega), ?_, ?_⟩
  · apply Rule30Diagonals.cell_eq_false_of_gt; omega
  · apply Rule30Diagonals.cell_eq_false_of_gt; omega

theorem diff_xor_local : ∀ al ar br hl hc hr kl kc kr : Bool,
    xor (xor (xor hl kl) ((!br) && xor hc kc)) ((!al) && xor hr kr) =
    xor (xor (xor hl ((!br) && hc)) ((!al) && hr))
        (xor (xor kl ((!br) && kc)) ((!al) && kr)) := by decide +kernel

theorem diff_xor (A B h k : Int → Bool) (p : Int) :
    diffStep A B (fun q => xor (h q) (k q)) p =
      xor (diffStep A B h p) (diffStep A B k p) :=
  diff_xor_local (A p) (A (p+1)) (B (p+1))
    (h (p-1)) (h p) (h (p+1)) (k (p-1)) (k p) (k (p+1))

theorem actual_local : ∀ al ac ar bl bc br : Bool,
    xor (xor (xor al bl) ((!br) && xor ac bc)) ((!ac) && xor ar br) =
      xor (rule al ac ar) (rule bl bc br) := by decide +kernel

theorem actual_difference (U V t : Nat) (p : Int) :
    diffStep (cell (U+t)) (cell (V+t))
      (fun q => xor (cell (U+t) q) (cell (V+t) q)) p =
      xor (cell (U+(t+1)) p) (cell (V+(t+1)) p) := by
  rw [show U+(t+1)=(U+t)+1 by omega,show V+(t+1)=(V+t)+1 by omega]
  exact actual_local
    (cell (U+t) (p-1)) (cell (U+t) p) (cell (U+t) (p+1))
    (cell (V+t) (p-1)) (cell (V+t) p) (cell (V+t) (p+1))

theorem common_flip_local : ∀ ac ar bc br hc hr : Bool,
    ((xor ar br) && hc) = ((xor ac bc) && hr) →
    ((xor ar br) && xor (xor ac bc) hc) =
      ((xor ac bc) && xor (xor ar br) hr) := by decide +kernel

def field (U V t : Nat) (p : Int) : Bool :=
  xor (xor (cell (U+t) p) (cell (V+t) p)) (evol (unit U) t p)

theorem field_mode (U V E H t : Nat)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (he : 2*H+1 ≤ E) (hUV : V+2*H+3 ≤ U) (ht : t ≤ H) :
    (∀ p, diffStep (cell (U+t)) (cell (V+t)) (field U V t) p =
      field U V (t+1) p) ∧
    Common (cell (U+t)) (cell (V+t)) (field U V t) := by
  obtain ⟨hd,hw⟩ := pulse_mode U V E H t hgap he hUV ht
  constructor
  · intro p
    unfold field
    rw [diff_xor, actual_difference, hd]
  · intro p
    exact common_flip_local _ _ _ _ _ _ (hw p)

theorem field_subset (U V : Nat) (hUV : V < U) :
    Subset (cell U) (cell V) (field U V 0) := by
  intro p
  by_cases hp : p=U
  · subst p
    have ha : cell U (U : Int)=true := by
      simpa [Rule30Diagonals.R] using Rule30Diagonals.R_zero U
    have hb := Rule30Diagonals.cell_eq_false_of_gt V (U : Int) (by omega)
    simp [field, evol, unit, ha, hb]
  · simp [field, evol, unit, hp]

theorem field_left (U V t : Nat) (hUV : V < U) :
    field U V t (-(U : Int)-t)=true := by
  have ha : cell (U+t) (-(U : Int)-t)=true := by
    rw [show -(U : Int)-t = -((U+t : Nat) : Int) by omega]
    exact Rule30Jen.cell_left_edge (U+t)
  have hb := Rule30Jen.cell_eq_false_of_lt (V+t) (-(U : Int)-t) (by omega)
  have hp : evol (unit U) t (-(U : Int)-t)=false := by
    cases hc : evol (unit U) t (-(U : Int)-t) with
    | false => rfl
    | true => have := pulse_support U t (-(U : Int)-t) hc; omega
  simp [field,ha,hb,hp]

theorem field_center (U V H t : Nat) (hU : H < U) (ht : t ≤ H)
    (heq : cell (U+t) 0=cell (V+t) 0) : field U V t 0=false := by
  have hp : evol (unit U) t 0=false := by
    cases hc : evol (unit U) t 0 with
    | false => rfl
    | true => have := pulse_support U t 0 hc; omega
  simp [field,heq,hp]

theorem field_right_white (U V E : Nat) (hVU : V ≤ U)
    (hq : U-V ≤ E)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (p : Int) (hp : (V : Int)<p) : field U V 0 p=false := by
  have ha := hgap p (by omega)
  have hb := Rule30Diagonals.cell_eq_false_of_gt V p hp
  simp [field,evol,ha,hb]

theorem field_right_black (U V E : Nat) (hVU : V < U)
    (hq : U-V ≤ E)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p) :
    field U V 0 V=true := by
  have ha := hgap V (by omega)
  have hb : cell V (V : Int)=true := by
    simpa [Rule30Diagonals.R] using Rule30Diagonals.R_zero V
  simp [field,evol,ha,hb,unit,show (V : Int)≠U by omega]

/-- The rightmost bit of every upper-bounded auxiliary field advances by one.
This backward version does not assume W or physical coefficient evolution. -/
theorem preimage_right_edge (A B g h : Int → Bool) (U V : Nat)
    (hVU : V ≤ U) (hg : ∀ p : Int, (U : Int) ≤ p → g p=false)
    (hh : ∀ p : Int, (V : Int)<p → h p=false) (hb : h V=true)
    (hs : ∀ p, diffStep A B g p=h p) : g ((V : Int)-1)=true := by
  have key : ∀ n : Nat, n ≤ U-V →
      g ((U : Int)-n)=false ∧ g ((U : Int)-n+1)=false := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hg U (by omega),hg ((U : Int)+1) (by omega)⟩
    | succ n ih =>
      intro hn
      obtain ⟨hc,hr⟩ := ih (by omega)
      have hd := hs ((U : Int)-n)
      have hz := hh ((U : Int)-n) (by omega)
      have hl : g ((U : Int)-n-1)=false := by
        simpa [diffStep,hc,hr,hz] using hd
      constructor
      · rw [show (U : Int)-((n+1 : Nat) : Int)=(U : Int)-n-1 by omega]
        exact hl
      · rw [show (U : Int)-((n+1 : Nat) : Int)+1=(U : Int)-n by omega]
        exact hc
  obtain ⟨hc,hr⟩ := key (U-V) (by omega)
  have pos : (U : Int)-((U-V : Nat) : Int)=V := by omega
  rw [pos] at hc hr
  have hd := hs (V : Int)
  simpa [diffStep,hc,hr,hb] using hd

theorem field_nonlift (U V E : Nat) (hV : 1 ≤ V) (hVU : V < U)
    (hq : U-V ≤ E)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (hprior : cell (U-1) ((V : Int)-1)=true) :
    ¬ ∃ g : Int → Bool, Subset (cell (U-1)) (cell (V-1)) g ∧
      ∀ p, diffStep (cell (U-1)) (cell (V-1)) g p=field U V 0 p := by
  rintro ⟨g,hsub,hstep⟩
  have upper : ∀ p : Int, (U : Int) ≤ p → g p=false := by
    intro p hp
    have ha := Rule30Diagonals.cell_eq_false_of_gt (U-1) p (by omega)
    have hb := Rule30Diagonals.cell_eq_false_of_gt (V-1) p (by omega)
    have hs := hsub p
    cases hc : g p <;> simp_all
  have forced := preimage_right_edge _ _ g (field U V 0) U V (by omega) upper
    (field_right_white U V E (by omega) hq hgap)
    (field_right_black U V E hVU hq hgap) hstep
  have hb : cell (V-1) ((V : Int)-1)=true := by
    rw [← show ((V-1 : Nat) : Int)=(V : Int)-1 by omega]
    simpa [Rule30Diagonals.R] using Rule30Diagonals.R_zero (V-1)
  have bad := hsub ((V : Int)-1)
  simp [hprior,hb,forced] at bad

theorem field_white_left (U V t : Nat) (hVU : V ≤ U) (p : Int)
    (hp : p < -(U : Int)-t) : field U V t p=false := by
  have ha := Rule30Jen.cell_eq_false_of_lt (U+t) p (by omega)
  have hb := Rule30Jen.cell_eq_false_of_lt (V+t) p (by omega)
  have hc : evol (unit U) t p=false := by
    cases hx : evol (unit U) t p with
    | false => rfl
    | true => have := pulse_support U t p hx; omega
  simp [field,ha,hb,hc]

theorem field_white_right (U V t : Nat) (hVU : V ≤ U) (p : Int)
    (hp : (U : Int)+t < p) : field U V t p=false := by
  have ha := Rule30Diagonals.cell_eq_false_of_gt (U+t) p (by omega)
  have hb := Rule30Diagonals.cell_eq_false_of_gt (V+t) p (by omega)
  have hc : evol (unit U) t p=false := by
    cases hx : evol (unit U) t p with
    | false => rfl
    | true => have := pulse_support U t p hx; omega
  simp [field,ha,hb,hc]

/-- Continue by D for all time, including beyond the finite W/sensor window. -/
def evolved (U V : Nat) : Nat → Int → Bool
  | 0 => field U V 0
  | t+1 => fun p => diffStep (cell (U+t)) (cell (V+t)) (evolved U V t) p

theorem evolved_eq (U V E H t : Nat)
    (hgap : ∀ p : Int, (U : Int)-E ≤ p → cell U p=unit U p)
    (he : 2*H+1 ≤ E) (hUV : V+2*H+3 ≤ U) (ht : t ≤ H+1) :
    evolved U V t=field U V t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext p
    change diffStep (cell (U+t)) (cell (V+t)) (evolved U V t) p=field U V (t+1) p
    rw [ih (by omega)]
    exact (field_mode U V E H t hgap he hUV (by omega)).1 p

/-! The following finite data select an example with the sensor retained.
Every checkpoint is a kernel computation of the official integer recurrence. -/

-- CHECKPOINTS_INSERTED_HERE

theorem gap_256 (p : Int) (hp : (256 : Int)-23 ≤ p) :
    cell 256 p=unit 256 p := by
  by_cases hout : 256 < p
  · rw [Rule30Diagonals.cell_eq_false_of_gt _ _ hout]
    symm
    simp only [unit,decide_eq_false_iff_not]; omega
  · let j : Nat := (256-p).toNat
    have hj : j < 24 := by dsimp [j]; omega
    have heq : (256 : Int)-j=p := by dsimp [j]; omega
    have low : (a 256)%2^24=1 := by rw [checkpoint_256] <;> decide +kernel
    have bit := congrArg (fun x : Nat => x.testBit j) low
    simp only [Nat.testBit_mod_two_pow,hj,decide_true,Bool.true_and,testBit_a] at bit
    norm_num only [Nat.cast_ofNat] at bit
    rw [heq] at bit
    rw [bit]
    by_cases hz : j=0
    · have hp' : p=256 := by omega
      simp [unit,hz,hp']
    · have hp' : p≠256 := by omega
      simp only [unit,hp',decide_false]
      cases h : j with
      | zero => exact False.elim (hz h)
      | succ j => simp [Nat.testBit_succ]

theorem prior_255_at_236 : cell 255 236=true := by
  have hb := testBit_a 255 19
  have ha : a 255=advance 31 (a 224) := a_add 224 31
  rw [ha,checkpoint_224] at hb
  exact hb.symm.trans (by decide +kernel)

theorem center_agreement_6 : ∀ t : Nat, t ≤ 6 → cell (256+t) 0=cell (237+t) 0 := by
  have h : ∀ t : Fin 7,
      (advance t (a 256)).testBit (256+t) =
      (advance (13+t) (a 224)).testBit (237+t) := by
    rw [checkpoint_256,checkpoint_224]
    decide +kernel
  intro t ht
  have hh := h ⟨t,by omega⟩
  rw [← a_add 256 t,← a_add 224 (13+t)] at hh
  simpa only [testBit_a,show 224+(13+t)=237+t by omega,Int.sub_self] using hh

/-- A finite sensor-compatible obstruction to the proposed one-step closure.
The previous-subset failure holds even without imposing previous W. This is
not an all-time common-field counterexample and proves no prize statement. -/
theorem finite_sensor_nonlift : ∃ h : Nat → Int → Bool,
    Subset (cell 256) (cell 237) (h 0) ∧
    (∀ p : Int, p < -256 ∨ 256 < p → h 0 p=false) ∧
    (∀ t, t ≤ 6 → h t (-(256 : Int)-t)=true ∧
      ∀ p, p < -(256 : Int)-t → h t p=false) ∧
    (∀ t, t ≤ 6 → h t 0=false) ∧
    (∀ t, t ≤ 6 → Common (cell (256+t)) (cell (237+t)) (h t)) ∧
    (∀ t p, h (t+1) p=diffStep (cell (256+t)) (cell (237+t)) (h t) p) ∧
    (¬ ∃ g : Int → Bool, Subset (cell 255) (cell 236) g ∧
      ∀ p, diffStep (cell 255) (cell 236) g p=h 0 p) := by
  have heq : ∀ t, t ≤ 7 → evolved 256 237 t=field 256 237 t := by
    intro t ht
    exact evolved_eq 256 237 23 6 t gap_256 (by decide) (by decide) ht
  refine ⟨evolved 256 237,field_subset 256 237 (by decide),?_,?_,?_,?_,?_,?_⟩
  · intro p hp
    rcases hp with hp | hp
    · exact field_white_left 256 237 0 (by decide) p (by omega)
    · exact field_white_right 256 237 0 (by decide) p (by omega)
  · intro t ht
    rw [heq t (by omega)]
    exact ⟨field_left 256 237 t (by decide),field_white_left 256 237 t (by decide)⟩
  · intro t ht
    rw [heq t (by omega)]
    exact field_center 256 237 6 t (by decide) ht (center_agreement_6 t ht)
  · intro t ht
    rw [heq t (by omega)]
    exact (field_mode 256 237 23 6 t gap_256 (by decide) (by decide) ht).2
  · intro t p; rfl
  · exact field_nonlift 256 237 23 (by decide) (by decide) (by decide) gap_256 prior_255_at_236

end Rule30SensorClosureResearch
