from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
cut=188;width=192;mask=(1<<width)-1
f=lambda s:(s+int(s>=94))%2
current=sum((1 if t%2==0 else f(t//2))<<t for t in range(width));older=0
columns=[older,current]
for d in range(932):
    nxt=((current>>1)|(((current>>cut)&1)<<(width-1)))^(current|older)
    older,current=current,nxt&mask
    columns.append(current)
assert len(columns)==934
def nextd(d):return 906 if d==933 else d+1
def step(a,b):return (((b>>1)|(((b>>cut)&1)<<(width-1)))^(b|a))&mask
assert all(columns[nextd(nextd(d))]==step(columns[d],columns[nextd(d)]) for d in range(934))
text='def columns : Array Nat := #[\n'+',\n'.join('  '+hex(n) for n in columns)+'\n]\n'
source=(ROOT/'wiki_profile_template.lean').read_text(encoding='utf-8').replace('-- COLUMN_WORDS_INSERTED_HERE',text)
checks='\n'.join('theorem checked_'+str(b)+' : blockOK '+str(b)+'=true := by decide +kernel' for b in range(30))
checks+='\n\ntheorem all_blocks (b : Nat) (hb : b<30) : blockOK b=true := by\n  match b with\n'
checks+='\n'.join('  | '+str(b)+' => exact checked_'+str(b) for b in range(30))
checks+='\n  | n+30 => omega\n'
source=source.replace('-- BLOCK_CHECKS_INSERTED_HERE',checks)
target=ROOT/'Rule30Slip94Research.lean';target.write_text(source,encoding='utf-8',newline='\n')
print(json.dumps({'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'bytes':target.stat().st_size,'closed_columns':len(columns)}))
