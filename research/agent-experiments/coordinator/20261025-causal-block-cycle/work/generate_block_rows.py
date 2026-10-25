"""Generate untrusted finite row witnesses; every jump is kernel checked."""
from pathlib import Path
import json
root=Path(__file__).resolve().parent
onsets=sorted({r['onset'] for r in json.loads((root/'block-cycle-witnesses.json').read_text())['records']})
needed=sorted({n+d for n in onsets for d in [0,1,2,16,17,18]})
rows=[1]
for _ in range(max(needed)):rows.append(rows[-1]^((rows[-1]<<1)|(rows[-1]<<2)))
s=['module','public import Rule30Equivalents.IntegerRows','',
   '/-! Finite canonical seed rows for a block-rank obstruction. A generator supplies',
   'integers, but every 32-step jump and every final remainder is kernel checked. -/',
   '@[expose] public section','namespace Rule30BlockRowsResearch','open Rule30Equivalents.IntegerRows',
   'set_option maxRecDepth 10000','set_option maxHeartbeats 2000000','',
   'def step (x : Nat) : Nat := x ^^^ ((2*x) ||| (4*x))',
   'def advance : Nat → Nat → Nat','  | 0,x => x','  | k+1,x => step (advance k x)','',
   'theorem a_add (n k : Nat) : a (n+k)=advance k (a n) := by',
   '  induction k with','  | zero => rfl','  | succ k ih =>',
   '    change step (a (n+k))=step (advance k (a n))','    rw [ih]','',
   'theorem checkpoint_0 : a 0=1 := rfl','']
for n in range(32,max(needed)//32*32+1,32):
    prev=n-32
    s += [f'theorem checkpoint_{n} : a {n}={hex(rows[n])} := by',
          f'  calc a {n}=advance 32 (a {prev}) := a_add {prev} 32',
          f'    _=advance 32 {hex(rows[prev])} := congrArg (advance 32) checkpoint_{prev}',
          f'    _={hex(rows[n])} := by decide +kernel','']
for n in needed:
    base=n//32*32;rem=n-base
    s += [f'theorem row_{n} : a {n}={hex(rows[n])} := by',
          f'  calc a {n}=advance {rem} (a {base}) := a_add {base} {rem}',
          f'    _=advance {rem} {hex(rows[base])} := congrArg (advance {rem}) checkpoint_{base}',
          f'    _={hex(rows[n])} := by decide +kernel','']
s += ['end Rule30BlockRowsResearch','']
(root/'Rule30BlockRowsResearch.lean').write_text('\n'.join(s),encoding='utf-8',newline='\n')
print(json.dumps({'onsets':onsets,'needed_rows':len(needed),'checkpoints':max(needed)//32+1,'source_bytes':(root/'Rule30BlockRowsResearch.lean').stat().st_size}))
