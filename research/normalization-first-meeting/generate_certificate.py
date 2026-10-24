"""Generate the finite certificate; companion Lean modules prove stripe semantics."""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
states=json.loads((HERE/'normalization_meeting_automaton.states.json').read_text())
assert len(states)==2321
source=r'''import Ruliology.CellularAutomata.Rule30Prize

/-! Finite certificate for the paired-row machine. Companion modules prove
its all-size stripe-relation meaning. Numerical-normalizer equivalence and
infinite-trace completeness are not proved. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Rule30NormalizationMachineResearch

def tailNext (s : Nat) (b : Bool) : Nat :=
  match s, b with
  | 0, false => 0 | 0, true => 1
  | 1, false => 2 | 1, true => 3
  | 2, false => 4 | 2, true => 3
  | 3, false => 2 | 3, true => 4
  | _, _ => 4

def relStep (e : Nat) (a b allow : Bool) : Nat :=
  let ta := tailNext ((e / 8) / 5) a
  let tb := tailNext ((e / 8) % 5) b
  let valid := (e.testBit 0 && (a == b)) || (e.testBit 1 && !a && !b)
  let pending := allow && a && b && (ta == 1 || ta == 3) && (tb == 1 || tb == 3)
  8 * (5 * ta + tb) + 4 * (e.testBit 2 && (a == b)).toNat +
    2 * pending.toNat + valid.toNat

def first (h : Nat) (a : Bool) : Bool := xor a (h.testBit 0 || h.testBit 1)
def second (h : Nat) (a : Bool) : Bool := xor (first h a)
  (xor (h.testBit 0) (h.testBit 1 || h.testBit 2) ||
   xor (h.testBit 1) (h.testBit 2 || h.testBit 3))

def step (s v : Nat) : Option Nat :=
  let old := s >>> 32
  let marker := v.testBit 2
  if marker && old != 0 then none else
  let code := if marker then 1 else if old == 0 then 0 else min 4 (old + 1)
  let ha := (s >>> 24) % 16
  let hb := (s >>> 28) % 16
  let a := v.testBit 0
  let b := v.testBit 1
  let a1 := first ha a
  let b1 := first hb b
  if (code == 1 && a != b) || (code == 2 && a1 != b1) then none else
  let e0 := relStep (s % 256) a b (code == 0 || code ≤ 1)
  let e1 := relStep ((s >>> 8) % 256) a1 b1 (code == 0 || code ≤ 2)
  let e2 := relStep ((s >>> 16) % 256) (second ha a) (second hb b) (code == 0 || code ≤ 3)
  some (e0 + (e1 <<< 8) + (e2 <<< 16) +
    (((2 * ha + a.toNat) % 16) <<< 24) +
    (((2 * hb + b.toNat) % 16) <<< 28) + (code <<< 32))

def flush : Nat → Nat → Option Nat
  | 0, s => some s
  | n + 1, s => (step s 0).bind (flush n)

def accept (s t : Nat) : Bool :=
  (s >>> (8*t)).testBit 0 || (s >>> (8*t)).testBit 2

def endGood (s : Nat) : Bool :=
  if s >>> 32 == 0 then true else
  match flush 5 s with
  | none => true
  | some e => !(accept e 2 && !accept e 0 && !accept e 1)

inductive StateTree where
  | nil
  | node (key : Nat) (left right : StateTree)

def member : StateTree → Nat → Bool
  | .nil, _ => false
  | .node k l r, s => if s == k then true else if s < k then member l s else member r s

def allNodes : StateTree → (Nat → Bool) → Bool
  | .nil, _ => true
  | .node k l r, f => f k && (allNodes l f && allNodes r f)

def closedAt (p : StateTree) (s : Nat) : Bool :=
  (List.range 8).all fun v => match step s v with
    | none => true
    | some s' => member p s'

def initial : Nat := 4 + (4 <<< 8) + (4 <<< 16)
def certificate (p : StateTree) : Bool :=
  member p initial && allNodes p (fun s => closedAt p s && endGood s)

def pool : StateTree := __STATES__

theorem checked : certificate pool = true := by decide +kernel

end Rule30NormalizationMachineResearch
'''
def tree(xs):
    if not xs:return '.nil'
    middle=len(xs)//2
    return f'(.node {xs[middle]} {tree(xs[:middle])} {tree(xs[middle+1:])})'
source=source.replace('__STATES__',tree(states))
(HERE/'Rule30NormalizationMachineResearch.lean').write_text(source,encoding='utf-8',newline='\n')
print(json.dumps({'states':len(states),'source_bytes':len(source.encode()),'certificate_generated':True,'proof_verified_by_generator':False}))
