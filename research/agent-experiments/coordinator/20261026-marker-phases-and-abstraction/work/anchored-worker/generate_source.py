from pathlib import Path
import json
root=Path(__file__).resolve().parent
d=json.loads((root/'abstract-closure.json').read_bytes())['classes']
parts=[]
for name,key in [('seed','seeds'),('rank','rank_table'),('pred','pred_table'),('choice','choice_table'),('witness','witness_table')]:
    vals=[]
    for p in ['0','1']:
        a=d[p][key]
        lines=[','.join(map(str,a[i:i+32])) for i in range(0,len(a),32)]
        vals.append('[\n    '+',\n    '.join(lines)+']')
    parts.append('def '+name+'Table (p : Fin 2) : List Nat :=\n  if p.val=0 then '+vals[0]+'\n  else '+vals[1]+'\n')
template=(root/'AnchoredDefect.template.lean').read_text(encoding='utf-8')
(root/'AnchoredDefectAbstraction.lean').write_text(template.replace('@@TABLES@@','\n'.join(parts)),encoding='utf-8')
print('Generated exact finite rank/predecessor tables and semantic proof source.')
