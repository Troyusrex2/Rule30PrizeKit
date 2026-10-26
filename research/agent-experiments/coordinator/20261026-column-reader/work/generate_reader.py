from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
dfa=json.loads((ROOT/'learned-reader.json').read_bytes())['dfa']
prod=json.loads((ROOT/'invariance-product.json').read_bytes());assert prod['closed']
table='['+','.join('['+','.join(map(str,row))+']' for row in dfa['transitions'])+']'
def sym(i):return '('+str(bool(i>>1)).lower()+','+str(bool(i&1)).lower()+')'
allowed='[\n  '+',\n  '.join('⟨'+str(a)+','+str(b)+','+sym(p)+','+sym(q)+'⟩' for a,b,p,q in prod['states'])+']'
s=(ROOT/'reader_template.lean').read_text(encoding='utf-8').replace('__TABLE__',table).replace('__ALLOWED__',allowed)
(ROOT/'Rule30ColumnReaderResearch.lean').write_text(s,encoding='utf-8')
print(json.dumps({'product_states':len(prod['states']),'source_lines':len(s.splitlines())}))
