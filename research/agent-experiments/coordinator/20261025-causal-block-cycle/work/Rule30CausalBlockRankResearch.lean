module
public import Rule30BlockRowsResearch
public import Mathlib.Order.Defs.PartialOrder

/-! An obstruction to one precise causal block-rank template. A block is a
maximal contiguous disagreement word, decorated by its one-cell paired halo
and time phase mod16. No rank into ANY preorder can both be nonincreasing from
identically decorated causal parents and strictly decrease on every pure split.
Position-dependent ranks, larger halos, history, different block segmentation,
and global cross-block credit are outside this statement. Problem1 stays open. -/
@[expose] public section
namespace Rule30CausalBlockRankResearch
universe u
open Rule30Equivalents.IntegerRows Rule30BlockRowsResearch
open Ruliology.CellularAutomata

structure Descriptor where
  phase : Nat
  left : Nat
  word : List Nat
  right : Nat
  deriving DecidableEq

structure Located where
  lo : Nat
  desc : Descriptor
  deriving DecidableEq

def pairAt (a b i : Nat) : Nat := (a.testBit i).toNat+2*(b.testBit i).toNat
def different (a b i : Nat) : Bool := xor (a.testBit i) (b.testBit i)

/-- A nonempty maximal contiguous disagreement block, with its exact halo.
All witness blocks are away from bit zero, so no artificial boundary is used. -/
def blockCheck (a b : Nat) (p : Located) : Bool :=
  decide (0<p.lo) && !p.desc.word.isEmpty &&
  decide (p.desc.left=0 ∨ p.desc.left=3) &&
  decide (p.desc.right=0 ∨ p.desc.right=3) &&
  (p.desc.word.all fun v=>decide (v=1 ∨ v=2)) &&
  decide (pairAt a b (p.lo-1)=p.desc.left) &&
  decide (pairAt a b (p.lo+p.desc.word.length)=p.desc.right) &&
  ((List.range p.desc.word.length).all fun i=>
    decide (pairAt a b (p.lo+i)=p.desc.word.getD i 0))

def contains (p : Located) (i : Nat) : Bool :=
  decide (p.lo≤i ∧ i<p.lo+p.desc.word.length)

/-- Exactly all disagreement blocks meeting the child's two-step causal
interval [lo-4,hi]. Every listed parent really meets that interval. -/
def coverCheck (a b : Nat) (ps : List Located) (c : Located) : Bool :=
  decide (4≤c.lo) && !ps.isEmpty &&
  (ps.all fun p=>decide (p.lo≤c.lo+c.desc.word.length-1 ∧
    c.lo-4≤p.lo+p.desc.word.length-1)) &&
  ((List.range (c.desc.word.length+4)).all fun j=>
    different a b (c.lo-4+j)==ps.any (fun p=>contains p (c.lo-4+j)))

def Guard (n : Nat) : Prop :=
  Rule30Prize.center n=Rule30Prize.center (n+16) ∧
  Rule30Prize.center (n+1)=Rule30Prize.center (n+17) ∧
  Rule30Prize.center (n+2)=Rule30Prize.center (n+18)

/-- Actual canonical lag16 pair at onset n, advanced by two steps. IntegerRows
is linked to the official cell evolution by testBit_a and center_eq_testBit. -/
def Event (n : Nat) (ps : List Located) (c : Located) : Prop :=
  Guard n ∧
  (ps.all fun p=>blockCheck (a n*2^16) (a (n+16)) p && decide (p.desc.phase=n%16))=true ∧
  blockCheck (a (n+2)*2^16) (a (n+18)) c=true ∧ c.desc.phase=(n+2)%16 ∧
  coverCheck (a n*2^16) (a (n+16)) ps c=true

def WeakCausal {α : Type u} [Preorder α] (rank : Descriptor→α) : Prop :=
  ∀ n ps c d, Event n ps c → (∀ p∈ps, p.desc=d) → rank c.desc≤rank d

def StrictSplit {α : Type u} [Preorder α] (rank : Descriptor→α) : Prop :=
  ∀ n p c c', Event n [p] c → Event n [p] c' →
    c.lo+c.desc.word.length<c'.lo → rank c.desc<rank p.desc

def d0 : Descriptor := ⟨5,3,[1],3⟩
def d1 : Descriptor := ⟨7,3,[2],0⟩
def d2 : Descriptor := ⟨9,0,[2],0⟩
def d3 : Descriptor := ⟨11,3,[2,1,1],3⟩
def d4 : Descriptor := ⟨13,3,[2],3⟩
def d5 : Descriptor := ⟨15,3,[2,1],3⟩
def d6 : Descriptor := ⟨1,3,[1],3⟩
def d7 : Descriptor := ⟨3,3,[2],3⟩

theorem event0 : Event 37 [⟨45,d0⟩] ⟨47,d1⟩ := by
  simp only [Event,Guard,center_eq_testBit,Nat.reduceAdd,
    row_37,row_38,row_39,row_53,row_54,row_55]
  decide +kernel

theorem event1 : Event 887 [⟨1312,d1⟩,⟨1316,d1⟩] ⟨1316,d2⟩ := by
  simp only [Event,Guard,center_eq_testBit,Nat.reduceAdd,
    row_887,row_888,row_889,row_903,row_904,row_905]
  decide +kernel

theorem event2 : Event 89 [⟨42,d2⟩] ⟨42,d3⟩ := by
  simp only [Event,Guard,center_eq_testBit,Nat.reduceAdd,
    row_89,row_90,row_91,row_105,row_106,row_107]
  decide +kernel

theorem event3 : Event 507 [⟨22,d3⟩] ⟨22,d4⟩ := by
  simp only [Event,Guard,center_eq_testBit,Nat.reduceAdd,
    row_507,row_508,row_509,row_523,row_524,row_525]
  decide +kernel

theorem event3_sibling : Event 507 [⟨22,d3⟩] ⟨24,⟨13,3,[1],0⟩⟩ := by
  simp only [Event,Guard,center_eq_testBit,Nat.reduceAdd,
    row_507,row_508,row_509,row_523,row_524,row_525]
  decide +kernel

theorem event4 : Event 301 [⟨237,d4⟩] ⟨237,d5⟩ := by
  simp only [Event,Guard,center_eq_testBit,Nat.reduceAdd,
    row_301,row_302,row_303,row_317,row_318,row_319]
  decide +kernel

theorem event5 : Event 911 [⟨1024,d5⟩] ⟨1027,d6⟩ := by
  simp only [Event,Guard,center_eq_testBit,Nat.reduceAdd,
    row_911,row_912,row_913,row_927,row_928,row_929]
  decide +kernel

theorem event6 : Event 737 [⟨443,d6⟩] ⟨444,d7⟩ := by
  simp only [Event,Guard,center_eq_testBit,Nat.reduceAdd,
    row_737,row_738,row_739,row_753,row_754,row_755]
  decide +kernel

theorem event7 : Event 1011 [⟨728,d7⟩] ⟨730,d0⟩ := by
  simp only [Event,Guard,center_eq_testBit,Nat.reduceAdd,
    row_1011,row_1012,row_1013,row_1027,row_1028,row_1029]
  decide +kernel

/-- The target order can be unbounded, including an ordinal order. The failure
comes from a strict cycle of exact descriptors, not from a finite rank bound. -/
theorem no_causal_block_rank_univ {α : Type u} [Preorder α] (rank : Descriptor→α) :
    ¬ (WeakCausal rank ∧ StrictSplit rank) := by
  rintro ⟨hw,hs⟩
  have h0 : rank d1≤rank d0 := hw _ _ _ _ event0 (by simp)
  have h1 : rank d2≤rank d1 := hw _ _ _ _ event1 (by simp)
  have h2 : rank d3≤rank d2 := hw _ _ _ _ event2 (by simp)
  have h3 : rank d4<rank d3 := hs _ _ _ _ event3 event3_sibling (by decide)
  have h4 : rank d5≤rank d4 := hw _ _ _ _ event4 (by simp)
  have h5 : rank d6≤rank d5 := hw _ _ _ _ event5 (by simp)
  have h6 : rank d7≤rank d6 := hw _ _ _ _ event6 (by simp)
  have h7 : rank d0≤rank d7 := hw _ _ _ _ event7 (by simp)
  have hlo : rank d0≤rank d4 := le_trans h7 (le_trans h6 (le_trans h5 h4))
  have hhi : rank d4<rank d0 := lt_of_lt_of_le h3 (le_trans h2 (le_trans h1 h0))
  exact (lt_irrefl (rank d0)) (lt_of_le_of_lt hlo hhi)

/-- Fixed-universe headline for the unchanged checker. The polymorphic
theorem above is also included in its full kernel replay. -/
theorem no_causal_block_rank {α : Type} [Preorder α] (rank : Descriptor→α) :
    ¬ (WeakCausal rank ∧ StrictSplit rank) := no_causal_block_rank_univ rank

/-- Covers preorders in Type1, including the usual small-ordinal type. -/
theorem no_causal_block_rank_type_one {α : Type 1} [Preorder α] (rank : Descriptor→α) :
    ¬ (WeakCausal rank ∧ StrictSplit rank) := no_causal_block_rank_univ rank

end Rule30CausalBlockRankResearch
