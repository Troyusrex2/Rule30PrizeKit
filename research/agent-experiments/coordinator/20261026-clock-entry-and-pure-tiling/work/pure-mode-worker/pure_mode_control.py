"""Two exact block identities only; no orbit/clock/width sweep."""
from pathlib import Path
import json

blocks={
    1:{'A':'10110','u':'11010'},
    3:{'A':'1011000','u':'1101000'},
}
out={}
for gap,columns in blocks.items():
    out[gap]={}
    for column,word in columns.items():
        height=[0]
        for i,ch in enumerate(word):
            height.append(height[-1]+((-1)**i)*(ch=='0'))
        out[gap][column]={'word':word,'length':len(word),'height_at_even_start':height,
                          'drift':height[-1],'min':min(height),'max':max(height)}
        if column=='A':assert height[-1]==0 and min(height)==-1 and max(height)==0
        else:assert height[-1]==2 and min(height)==0 and max(height)==2
        assert len(word)%2==1

# Only four joins. This checks the limitation of closure: a long gap splits
# the parent's derivative into length-three and length-one blocks.
for gap,x in blocks.items():
    word=x['A']+'1'
    out[gap]['D_A_block']=''.join(str(int(word[i])^int(word[i+1])) for i in range(len(word)-1))
assert out[1]['D_A_block']=='11011'
assert out[3]['D_A_block']=='1101001'
root=Path(__file__).resolve().parent
(root/'pure-mode-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'blocks':2,'identities':4,'passed':True}))
