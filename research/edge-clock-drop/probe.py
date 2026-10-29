"""Independent intake audit and local period-drop obstruction tests."""
from pathlib import Path
import hashlib, json, time

ROOT = Path(__file__).resolve().parent
def period(x,q):
    h=1
    while h<q:
        if all(((x>>t)^(x>>((t+h)%q)))&1==0 for t in range(q)):return h
        h*=2
    return q
def delta(x,q):
    return x ^ ((x>>1)|((x&1)<<(q-1)))
def half_test(x,y,q):
    z=x|y;h=q//2
    return ((z & ((1<<h)-1)) == z>>h and (z & ((1<<h)-1)).bit_count()%2==0)
def main():
    audit=[]
    inbox=ROOT.parents[1]/'agent-inbox'
    for folder in sorted(inbox.glob('r30-coinailyzer-swarm-r4-05-*20261028*')):
        m=json.loads((folder/'manifest.json').read_text(encoding='utf-8-sig'))
        for a in m['artifacts']:
            actual=hashlib.sha256((folder/a['path']).read_bytes()).hexdigest()
            assert actual==a['sha256'],(folder,a['path'])
            audit.append({'response':folder.name,'path':a['path'],'sha256':actual})
    results=[]
    for q in [2,4,8,16]:
        n=0; witness=None
        for x in range(1<<q):
            if period(x,q)!=q:continue
            allowed=delta(x,q)
            y=allowed
            while True:
                if half_test(x,y,q):
                    n+=1
                    if witness is None:witness={'x':x,'y':y,'y_period':period(y,q)}
                if y==0:break
                y=(y-1)&allowed
        results.append({'q':q,'condition':'y subset delta(x); x exact period q; OR half-periodic with even half parity','count':n,'first':witness})
    result={'audit':audit,'generic_counterexample':{'q':4,'x':3,'y':12,'x_period':period(3,4),'y_period':period(12,4),'gap':half_test(3,12,4)},'local_tests':results}
    (ROOT/'INTAKE-AND-LOCAL.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
if __name__=='__main__':main()
