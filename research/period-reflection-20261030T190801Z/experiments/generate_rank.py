from pathlib import Path
import json
R=Path(__file__).resolve().parent
data=next(x for x in json.loads((R/'RELATIVE_RANK.json').read_text())['results'] if x['width']==4)
values=data['ranks'];assert len(values)==2048 and max(values)==6
# Input bits in index order are h,c,d1,d2,d3,x0,x1,x2,x3,x4,x5.
names=['h','c','d1','d2','d3','x0','x1','x2','x3','x4','x5']
order=[1,0,4,3,2,10,9,8,7,6,5]
def tree(items,remaining):
    vals={v for _,v in items}
    if len(vals)==1:return str(next(iter(vals)))
    bit=remaining[0];lo=[p for p in items if not p[0]>>bit&1];hi=[p for p in items if p[0]>>bit&1]
    a=tree(lo,remaining[1:]);b=tree(hi,remaining[1:])
    if a==b:return a
    return '(if '+names[bit]+' then '+b+' else '+a+')'
expression=tree(list(enumerate(values)),order)
s='''module
public import TemporalAncestry
public import QuietClock
@[expose] public section
namespace RelativeRank
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration QuietClock

def rank (x0 x1 x2 x3 x4 _x5 d1 d2 d3 c h : Bool) : Nat :=
  EXPR

set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

theorem rank_bound : ∀ x0 x1 x2 x3 x4 x5 d1 d2 d3 c h : Bool,
    rank x0 x1 x2 x3 x4 x5 d1 d2 d3 c h≤6 := by decide

theorem rank_certificate : ∀ x0 x1 x2 x3 x4 x5 d1 d2 d3 c h cp hp : Bool,
    (h=true → cp≠c) →
    xor x4 (x3||x2)=xor x4 (xor x3 d3||xor x2 d2) →
    xor x5 (x4||x3)=xor x5 (x4||xor x3 d3) →
    rank
      (xor x0 (c||h)) (xor x1 (x0||c)) (xor x2 (x1||x0))
      (xor x3 (x2||x1)) (xor x4 (x3||x2)) (xor x5 (x4||x3))
      (xor (xor x1 (x0||c)) (xor (xor x1 d1) (!x0||c)))
      (xor (xor x2 (x1||x0)) (xor (xor x2 d2) (xor x1 d1||!x0)))
      (xor (xor x3 (x2||x1)) (xor (xor x3 d3) (xor x2 d2||xor x1 d1))) cp hp
      +(if c then 1 else 0)≤rank x0 x1 x2 x3 x4 x5 d1 d2 d3 c h := by decide

end RelativeRank
'''.replace('EXPR',expression)
(R/'RelativeRank.lean').write_text(s,encoding='utf-8',newline='\n')
(R/'project').mkdir(exist_ok=True)
(R/'project/RelativeRank.lean').write_text(s,encoding='utf-8',newline='\n')
print(json.dumps(dict(expression_characters=len(expression),proof_source_bytes=len(s.encode()))))
