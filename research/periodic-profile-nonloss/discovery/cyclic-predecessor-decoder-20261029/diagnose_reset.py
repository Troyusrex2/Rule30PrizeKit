from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent;g=json.loads((ROOT/'PROFILE-GRAPH.json').read_text())['graphs'][-1]
for repeat in (0,1):
    labels={};witness=None
    for a,b in g['nodes']:
        for t in range(32):
            if ((b>>((t-1)%32))&1)!=repeat or ((b>>((t-2)%32))&1)!=repeat:continue
            key=(b>>t)&1;v=((a>>t)&1,a,b,t)
            if key in labels and labels[key][0]!=v[0]:witness={'input_repeat':str(repeat)*2,'next_input':key,'first':labels[key],'second':v};break
            labels[key]=v
        if witness:break
    print(json.dumps(witness))
