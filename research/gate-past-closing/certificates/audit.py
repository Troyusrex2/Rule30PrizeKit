"""Independent literal triangle replay and exact legal-prefix cover audit."""
from pathlib import Path
import json,itertools,time,hashlib,sys
ROOT=Path(__file__).resolve().parent
S={8,9,16,18,33,36,66,72,132,144}
INV={}
for future,center,right in itertools.product(range(2),repeat=3):
    choices=[left for left in range(2) if ((30>>(4*left+2*center+right))&1)==future]
    assert len(choices)==1;INV[future,center,right]=choices[0]

def replay(n,leaf):
    m=leaf['future_length'];f=leaf['future_word'];k=leaf['sync_column']
    histories=[h for h in range(1<<n) if all((((h|(f<<n))>>i)&255) in S for i in range(n))]
    assert len(histories)==leaf['legal_pasts'] and histories
    if k==0:
        assert len(histories)==1;return 0
    assert 1<=k<=2*m+1
    cols=[]
    for h in histories:
        gates=[((h|(f<<n))>>i)&1 for i in range(n+m)]
        boundary=[v for g in gates for v in (1-g,1)]
        cols.append(([0]*len(boundary),boundary))
    cells=0
    for column in range(1,k+1):
        signatures={(tuple(p[:2*n]),tuple(c[:2*n])) for p,c in cols}
        if column==k:
            assert len(signatures)==1, (n,leaf)
            return cells
        assert len(signatures)>1, 'claimed sync not earliest'
        nxt=[]
        for p,c in cols:
            assert len(c)>2*n
            out=[INV[c[t+1],c[t],p[t]] for t in range(len(c)-1)]
            cells+=len(out);nxt.append((c,out))
        cols=nxt

def cover(leaves):
    terminals={(v['future_length'],v['future_word']) for v in leaves}
    assert len(terminals)==len(leaves)
    nodes=set()
    for m,f in terminals:
        assert f>>m==0 and (f&255) in S
        assert all(((f>>i)&255) in S for i in range(m-7))
        for j in range(8,m):
            key=(j,f&((1<<j)-1));assert key not in terminals
            nodes.add(key)
    visited=set()
    def check(m,f):
        key=(m,f);assert key in terminals or key in nodes
        visited.add(key)
        if key in terminals:return
        for b in (0,1):
            extension=f|(b<<m)
            if ((extension>>(m-7))&255) in S:check(m+1,extension)
    for f in S:check(8,f)
    assert visited==nodes|terminals
    return len(visited)

def audit(file):
    started=time.monotonic();d=json.loads(file.read_text());r=d['result'];assert r['complete_cover']
    count=cover(d['terminal_leaves']);cells=0
    for leaf in d['terminal_leaves']:cells+=replay(r['n'],leaf)
    return {'file':file.name,'certificate_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'n':r['n'],'terminal_leaves':len(d['terminal_leaves']),'cover_nodes':count,'literal_inverse_cells':cells,'max_sync_column':r['max_sync_column'],'passed':True,'seconds':time.monotonic()-started,'kernel_verified':False}

if __name__=='__main__':
    paths=[ROOT/p for p in sys.argv[1:]] if len(sys.argv)>1 else [ROOT/f'n{n}-CERTIFICATE.json' for n in range(3,8)]+[ROOT/'n8-cap128-CERTIFICATE.json']
    out=[]
    for file in paths:
        r=audit(file);out.append(r);print(json.dumps(r),flush=True)
        (ROOT/(file.name.replace('-CERTIFICATE.json','-AUDIT.json'))).write_text(json.dumps(r,indent=2)+'\n')
        (ROOT/'AUDIT.json').write_text(json.dumps({'results':out,'auditor_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},indent=2)+'\n')
