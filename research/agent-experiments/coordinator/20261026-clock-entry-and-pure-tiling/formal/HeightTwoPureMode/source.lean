import HeightTwoDescent

/-! Uniform height bound for arbitrary concatenations of the two pure mixed
blocks. The actual-parent application retains its explicit temporal tiling
premise; classification of all low-height traces into this grammar is not
asserted. -/
namespace HeightTwoPureMode
open CedarSafetySoundness CedarSafety HeightOneSemantics HeightTwoNearReturn
open RootEventHeight
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Both permitted blocks are prefixes of 1011000, of length five or seven. -/
def pattern : Nat → Bool
  | 0 => true
  | 1 => false
  | 2 => true
  | 3 => true
  | _ => false

def Tiled (b : Nat → Bool) (cut len : Nat → Nat) : Prop :=
  cut 0=0 ∧ ∀ n, (len n=5 ∨ len n=7) ∧ cut (n+1)=cut n+len n ∧
    ∀ i, i<len n → b (cut n+i)=pattern i

theorem height_congr (b c : Nat → Bool) (T : Nat)
    (h : ∀ t, t<T → b t=c t) : whiteHeight b T=whiteHeight c T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [whiteHeight,whiteHeight,ih (fun t ht => h t (by omega)),h T (by omega)]

theorem height_shift (b : Nat → Bool) (s T : Nat) :
    whiteHeight b (s+T)=whiteHeight b s+sign s*whiteHeight (fun t => b (s+t)) T := by
  induction T with
  | zero => simp [whiteHeight]
  | succ T ih =>
      rw [show s+(T+1)=(s+T)+1 by omega,whiteHeight,ih,whiteHeight,
        HeightOneLogic.sign_add]
      ring

theorem block_certificate :
    whiteHeight pattern 5=0 ∧ whiteHeight pattern 7=0 ∧
    ∀ i : Fin 8, -1≤whiteHeight pattern i.val ∧ whiteHeight pattern i.val≤0 := by
  decide +kernel

theorem boundary_height (b : Nat → Bool) (cut len : Nat → Nat)
    (h : Tiled b cut len) (n : Nat) : whiteHeight b (cut n)=0 := by
  induction n with
  | zero => rw [h.1];rfl
  | succ n ih =>
      have hn := h.2 n
      rw [hn.2.1,height_shift,ih]
      have he := height_congr (fun t => b (cut n+t)) pattern (len n) hn.2.2
      rw [he]
      rcases hn.1 with hl|hl <;> rw [hl] <;>
        simp only [block_certificate.1,block_certificate.2.1,mul_zero,add_zero]

theorem covering (cut len : Nat → Nat) (h0 : cut 0=0)
    (hl : ∀ n, 0<len n) (hc : ∀ n, cut (n+1)=cut n+len n) :
    ∀ t, ∃ n i, t=cut n+i ∧ i<len n := by
  intro t
  induction t with
  | zero => exact ⟨0,0,by omega,hl 0⟩
  | succ t ih =>
      obtain ⟨n,i,ht,hi⟩ := ih
      by_cases hn : i+1<len n
      · exact ⟨n,i+1,by omega,hn⟩
      · exact ⟨n+1,0,by have h := hc n;omega,hl (n+1)⟩

/-- Any infinite concatenation of 10110 and 1011000, with arbitrary choices,
has signed white-height contained in [-1,1]. No period is assumed. -/
theorem tiled_span_two (b : Nat → Bool) (cut len : Nat → Nat)
    (h : Tiled b cut len) : SpanTwo b := by
  refine ⟨-1,?_⟩
  intro t
  have hl : ∀ n, 0<len n := by intro n;rcases (h.2 n).1 with hn|hn <;> omega
  obtain ⟨n,i,rfl,hi⟩ := covering cut len h.1 hl (fun n => (h.2 n).2.1) t
  rw [height_shift,boundary_height b cut len h n,zero_add]
  have he := height_congr (fun t => b (cut n+t)) pattern i
    (fun j hj => (h.2 n).2.2 j (by omega))
  rw [he]
  have hi8 : i<8 := by rcases (h.2 n).1 with hn|hn <;> omega
  have hb := block_certificate.2.2 ⟨i,hi8⟩
  change -1≤whiteHeight pattern i ∧ whiteHeight pattern i≤0 at hb
  rcases sign_cases (cut n) with hs|hs <;> rw [hs] <;> simp only [one_mul,neg_one_mul] <;> omega

/-- Actual finite-white ancestry is retained: the tiled column is the
immediate older prefix, whose whole-word nonreturn follows from the child's
height band and the independently verified near-return obstruction. -/
theorem actual_parent_descent (xs : List Bool) (a b : Bool)
    (cut len : Nat → Nat) (ht : Tiled (tr (xs++[a])) cut len)
    (hh : SpanTwo (tr (xs++[a,b])))
    (hn : evolution 8 (xs++[a,b])≠xs++[a,b]) :
    SpanTwo (tr (xs++[a])) ∧ evolution 8 (xs++[a])≠xs++[a] ∧
      (xs++[a]).length<(xs++[a,b]).length := by
  refine ⟨tiled_span_two _ cut len ht,?_,by simp⟩
  intro hr
  have hc := height_two_short_extension (xs++[a]) [b] hr (by simp)
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hc
  have hh' := hh
  rw [HeightTwoDescent.trace_function] at hh'
  exact hn (hc hh')

/-- Minimum width is taken over every height-two/nonreturn word, not merely
over words with this grammar and not over Safe words. -/
theorem minimal_height_two_not_tiled (xs : List Bool) (a b : Bool)
    (hh : SpanTwo (tr (xs++[a,b])))
    (hn : evolution 8 (xs++[a,b])≠xs++[a,b])
    (hm : ∀ ys : List Bool, ys.length<(xs++[a,b]).length →
      SpanTwo (tr ys) → evolution 8 ys=ys)
    (cut len : Nat → Nat) : ¬ Tiled (tr (xs++[a])) cut len := by
  intro ht
  obtain ⟨hs,hr,hl⟩ := actual_parent_descent xs a b cut len ht hh hn
  exact hr (hm _ hl hs)

end HeightTwoPureMode
