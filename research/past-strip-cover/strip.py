from pathlib import Path
import json,time,sys,hashlib
import psutil
ROOT=Path(__file__).resolve().parent
S={8,9,16,18,33,36,66,72,132,144}

def pasts(n,future):
    # Chronological little-endian gate words: prepend a bit at the near end.
    hs=[0]
    for j in range(n):
        nxt=[]
        for h in hs:
            for b in (0,1):
                value=b|(h<<1)|(future<<(j+1))
                if value&255 in S:nxt.append(b|(h<<1))
        hs=nxt
    return hs

def physical(word,size):
    return sum((1 if t%2 else 1-((word>>(t//2))&1))<<t for t in range(2*size))

def sync(n,future,m):
    hs=pasts(n,future)
    assert hs
    if len(hs)==1:return 0,len(hs)
    states=[(0,physical(h|(future<<n),n+m)) for h in hs]
    mask=(1<<(2*n))-1
    for k in range(1,2*m+2):
        signature={(p&mask,c&mask) for p,c in states}
        if len(signature)==1:return k,len(hs)
        states=[(c,(c>>1)^(c|p)) for p,c in states]
    return None,len(hs)

def check_extendable():
    vertices={(w>>1) for w in S}|{w&127 for w in S}
    edges={v:[(v>>1)|(b<<6) for b in (0,1) if v|(b<<7) in S] for v in vertices}
    # Every suffix actually used has an outgoing edge, hence an infinite path.
    assert all(edges.values())
    return len(vertices)

def run(n,cap=64,resume=False):
    started=time.monotonic();frontier=[(8,f) for f in sorted(S)];leaves=[];processed=0;hist=[];stop=None
    if resume:
        previous=f'n{n}-cap{resume}-CERTIFICATE.json' if type(resume) is int else f'n{n}-CERTIFICATE.json'
        old=json.loads((ROOT/previous).read_text())
        frontier=[tuple(x) for x in old['unresolved_frontier']];leaves=old['terminal_leaves']
        assert frontier and len(set(frontier))==len(frontier)
    while frontier:
        nxt=[];pruned=0
        for m,f in frontier:
            processed+=1;k,count=sync(n,f,m)
            if k is not None:
                leaves.append({'future_length':m,'future_word':f,'sync_column':k,'legal_pasts':count});pruned+=1
            else:
                if m>=cap:nxt.append((m,f));stop='future_length_cap';continue
                for b in (0,1):
                    extended=f|(b<<m)
                    if ((extended>>(m-7))&255) in S:nxt.append((m+1,extended))
            if processed>=200000:stop='prefix_cap';break
            if time.monotonic()-started>90:stop='time_cap';break
            if processed%64==0:
                assert psutil.Process().memory_info().rss<1024**3
                assert psutil.virtual_memory().available>2*1024**3
        hist.append({'length':frontier[0][0],'processed':len(frontier),'pruned':pruned,'remaining':len(nxt)})
        if frontier[0][0]%8==0: print(json.dumps({'n':n,**hist[-1]}),flush=True)
        if stop:
            # Save unprocessed current branches too: never report a partial pass.
            frontier=nxt+frontier[(processed-sum(h['processed'] for h in hist[:-1])):];break
        frontier=nxt
    out={'n':n,'complete_cover':not frontier and stop is None,'stop':stop,'processed':processed,'leaves':len(leaves),'max_sync_column':max((v['sync_column'] for v in leaves),default=None),'max_future_length':max((v['future_length'] for v in leaves),default=None),'frontier_count':len(frontier),'seconds':time.monotonic()-started,'kernel_verified':False,'history':hist}
    label=f'n{n}' if cap==64 else f'n{n}-cap{cap}'
    (ROOT/f'{label}-CERTIFICATE.json').write_text(json.dumps({'result':out,'terminal_leaves':leaves,'unresolved_frontier':frontier},separators=(',',':'))+'\n')
    (ROOT/f'{label}-RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='history'}),flush=True)
    return out

if __name__=='__main__':
    check_extendable()
    run(int(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 64,'--resume' in sys.argv)
