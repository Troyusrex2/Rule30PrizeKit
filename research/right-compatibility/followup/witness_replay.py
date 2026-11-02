"""Independent literal Rule30-table replay; no graph package or Lean trust."""
import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parent
def rule(a,b,c):return (30>>(4*a+2*b+c))&1
def row(v):return [(v>>i)&1 for i in range(6)]
def step(v,c,b):
    r=row(v);extended=[c]+r+[b]
    return sum(rule(*extended[i:i+3])<<i for i in range(6))
def main():
    data=json.loads((ROOT/'recurrent-result.json').read_text())
    loops=data['witness']['loops'];S={8,9,16,18,33,36,66,72,132,144}
    count=0
    for choice,loop in enumerate(loops):
        assert len(loop)==19 and loop[0]['before']==[63,17,7]
        assert loop[-1]['after']==loop[0]['before']
        word=[]
        for i,e in enumerate(loop):
            v=e['before'][0];u=e['after'][0];a,b=e['inputs']
            mid=step(v,1,a);end=step(mid,0,b)
            assert end==u
            f=e['f'];assert rule(f,0,mid&1)==1
            assert rule(1,1,v&1)==0
            assert f==int(bool(v&3));word.append(f);count+=2
            assert e['after']==loop[(i+1)%19]['before']
        assert word[5]==choice
        code=sum((1-bit)<<i for i,bit in enumerate(word[:8]))
        assert code not in S
    for a in range(2):
        for b in range(2):
            word=[e['f'] for e in loops[a]+loops[b]]
            assert all(word[i:i+2]!=[0,0] for i in range(37))
            assert all(word[i:i+5]!=[1]*5 for i in range(34))
    result={'status':'pass','literal_single_steps':count,'block_boundary_pairs':4,
      'length':19,'read_offset':5,'bad_S_codes':[162,10],
      'scope':'finite strip witness only; infinite claims separately checked in Lean',
      'witness_sha256':hashlib.sha256((ROOT/'recurrent-result.json').read_bytes()).hexdigest()}
    (ROOT/'literal-validation.json').write_text(json.dumps(result,indent=2));print(json.dumps(result))
if __name__=='__main__':main()
