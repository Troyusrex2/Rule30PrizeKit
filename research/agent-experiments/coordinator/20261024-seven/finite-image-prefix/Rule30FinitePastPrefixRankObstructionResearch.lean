import Rule30FiniteImagePumpResearch

/-! A unit-scale signed prefix-reader obstruction on an actual finite-image
domain. The lower-bound premise includes a real finite predecessor, its
black head and preceding free one, and thirteen forward alternating steps.
This rules out the specified rank, not CQ01 or the prize problem. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Rule30FinitePastPrefixRankObstructionResearch
open Ruliology.CellularAutomata.Rule30ZeroBoundary
open Rule30FiniteLeftWordResearch (row next Canonical row_support row_next zrow_prefix)
open Rule30WeightedWordPumpResearch (run score score_append)
open Rule30VacuumPrefixRankObstructionResearch
  (transition reader_absorbing Safe13 w1 w2 cycle_extension pumped_prefix pumped_safe)
open Rule30FiniteImagePumpResearch (HasPastOne sink_cost_nonnegative unit_scale)

def startWord : List Bool := w2
def middleWord : List Bool := next startWord
def endWord : List Bool := next middleWord
def commonWord : List Bool := startWord.take 6

def tally (b : Bool) : List Bool → Nat
  | [] => 0
  | a::w => tally b w+if a=b then 1 else 0

theorem score_sink (C : Nat → Bool → Int) (w : List Bool) :
    score transition C 1 1 w=(tally false w:Int)*C 1 false+(tally true w:Int)*C 1 true := by
  induction w with
  | nil => simp [score,tally]
  | cons a w ih =>
    rw [score,reader_absorbing,ih]
    cases a with
    | false =>
      simp only [tally,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
      rw [show ((tally false w+1:Nat):Int)=(tally false w:Int)+1 by omega,Int.add_mul]
      simp only [Int.one_mul]
      omega
    | true =>
      simp only [tally,Bool.true_eq_false,↓reduceIte,Nat.add_zero]
      rw [show ((tally true w+1:Nat):Int)=(tally true w:Int)+1 by omega,Int.add_mul]
      simp only [Int.one_mul]
      omega

theorem reader_common : run transition 0 commonWord=1 := by decide +kernel
theorem end_common : endWord.take 6=commonWord := by decide +kernel

theorem tail_counts :
    tally false (endWord.drop 6)=tally false (startWord.drop 6)+1 ∧
    tally true (endWord.drop 6)=tally true (startWord.drop 6)+3 := by decide +kernel

theorem score_tail (C : Nat → Bool → Int) (w : List Bool) (hw : w.take 6=commonWord) :
    score transition C 1 0 w=score transition C 1 0 commonWord+
      score transition C 1 1 (w.drop 6) := by
  have he : commonWord++w.drop 6=w := by rw [←hw];exact List.take_append_drop 6 w
  have h:=score_append transition C 1 commonWord (w.drop 6) 0
  rw [he,reader_common,unit_scale,Int.one_mul] at h
  exact h

theorem score_difference (C : Nat → Bool → Int) :
    score transition C 1 0 endWord=score transition C 1 0 startWord+C 1 false+3*C 1 true := by
  rw [score_tail C endWord end_common,score_tail C startWord rfl,score_sink,score_sink,
    tail_counts.1,tail_counts.2]
  rw [show ((tally false (startWord.drop 6)+1:Nat):Int)=
      (tally false (startWord.drop 6):Int)+1 by omega,
    show ((tally true (startWord.drop 6)+3:Nat):Int)=
      (tally true (startWord.drop 6):Int)+3 by omega]
  simp only [Int.add_mul,Int.one_mul]
  omega

theorem start_canonical : Canonical startWord :=
  Rule30VacuumPrefixRankObstructionResearch.w2_canonical

theorem start_safe : Safe13 startWord 0 := by
  have h:=pumped_safe 1
  simpa only [startWord,Rule30WeightedWordPumpResearch.copies,List.nil_append,←cycle_extension] using h

theorem start_has_past : HasPastOne startWord := by
  refine ⟨row w1,⟨w1.length,row_support w1⟩,?_,?_,?_⟩
  · decide +kernel
  · exact Rule30VacuumPrefixRankObstructionResearch.second_free
  · exact Rule30VacuumPrefixRankObstructionResearch.physical_second

theorem physical_first : row middleWord=zrow (row startWord) 2 := row_next startWord
theorem physical_second : row endWord=zrow (row middleWord) 2 := row_next middleWord

theorem middle_prefix : ∀ d,d≤28 → row middleWord d=
    zrow Rule30CriticalChargeOneCoreResearch.left 2 d := by
  intro d hd
  rw [physical_first]
  apply zrow_prefix 30 (t:=2) (d:=d) (h:=?_) (by omega)
  intro i hi
  have h:=pumped_prefix 1 i hi
  simpa only [startWord,Rule30WeightedWordPumpResearch.copies,List.nil_append,←cycle_extension] using h

theorem middle_safe : Safe13 middleWord 1 := by
  have hp:=zrow_prefix 28 middle_prefix
  constructor
  · intro i hi
    rw [hp (2*i) 1 (by omega),←zrow_shift,show 2+2*i=2*(i+1) by omega]
    exact Rule30CriticalChargeOneCoreResearch.left_inX (i+1)
  · intro i hi
    rw [hp (2*i+1) 1 (by omega),←zrow_shift,show 2+(2*i+1)=2*(i+1)+1 by omega]
    exact Rule30CriticalChargeOneCoreResearch.left_free (i+1)

theorem start_free : zrow (row startWord) 1 1=false := by decide +kernel
theorem middle_free : zrow (row middleWord) 1 1=true := by decide +kernel
theorem middle_canonical : Canonical middleWord := by unfold Canonical;decide +kernel
theorem end_canonical : Canonical endWord := by unfold Canonical;decide +kernel

theorem middle_has_past_zero : ∃ P : Nat → Bool,
    FinSupp P ∧ P 1=true ∧ zrow P 1 1=false ∧ row middleWord=zrow P 2 := by
  refine ⟨row startWord,⟨startWord.length,row_support startWord⟩,?_,start_free,physical_first⟩
  decide +kernel

theorem no_unit_scale_finite_past_prefix_rank
    (C0 C1 : Nat → Bool → Int) (H0 H1 B : Int)
    (hb : ∀ w,Canonical w → Safe13 w 0 → HasPastOne w →
      B≤H1+score transition C1 1 0 w)
    (hfirst : H0+score transition C0 1 0 middleWord < H1+score transition C1 1 0 startWord)
    (hsecond : H1+score transition C1 1 0 endWord ≤ H0+score transition C0 1 0 middleWord) :
    False := by
  have h0:=sink_cost_nonnegative C1 H1 B hb false
  have h1:=sink_cost_nonnegative C1 H1 B hb true
  have hd:=score_difference C1
  omega

end Rule30FinitePastPrefixRankObstructionResearch
