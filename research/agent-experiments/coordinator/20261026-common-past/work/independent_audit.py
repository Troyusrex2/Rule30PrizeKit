"""Independent exact prefix/inverse controls and literal physical coordinates."""
from pathlib import Path
import ast,itertools,json,random
ROOT=Path(__file__).resolve().parent
def m(x):return x^((x<<1)|(x<<2))
def d(a,b,h):return h^((~(b<<2))&(h<<1))^((~(a<<1))&(h<<2))
def w(a,b,h):delta=a^b;return ((delta<<1)&h)==((h<<1)&delta)
def inverse(a,b,y,n):
    g=0
    for j in range(n):
        bit=(y>>j)&1
        if j>=1:bit^=(1^((b>>(j-2))&1) if j>=2 else 1)*((g>>(j-1))&1)
        if j>=2:bit^=(1^((a>>(j-1))&1))*((g>>(j-2))&1)
        g|=bit<<j
    return g
cases=0;recombinations=0
for n in range(1,5):
    mask=(1<<n)-1;period=1<<(n-1)
    for a,b,h in itertools.product(range(1<<n),repeat=3):
        assert inverse(a,b,d(a,b,h)&mask,n)==h
        pre=inverse(a,b,h,n);assert d(a,b,pre)&mask==h
        aa,bb,hh=a,b,h
        for t in range(period):aa,bb,hh=m(aa)&mask,m(bb)&mask,d(aa,bb,hh)&mask
        assert (aa,bb,hh)==(a,b,h)
        if not h&~(a^b) and w(a,b,h):
            assert m(a^h)==(m(a)^d(a,b,h));recombinations+=1
        cases+=1
# Direct physical cell-set evolution: bit j represents position t-j.
rng=random.Random(302026);cells=0
for case in range(24):
    a,b,h=[rng.randrange(64) for _ in range(3)]
    A={-j for j in range(6) if a>>j&1};B={-j for j in range(6) if b>>j&1};H={-j for j in range(6) if h>>j&1}
    for t in range(20):
        for p in range(-6-t,t+2):
            idx=t-p
            assert (p in A)==bool(idx>=0 and (a>>idx)&1)
            assert (p in B)==bool(idx>=0 and (b>>idx)&1)
            assert (p in H)==bool(idx>=0 and (h>>idx)&1);cells+=3
        region=range(-7-t,t+2)
        Hn={p for p in region if ((p-1 in H)^((p+1 not in B) and (p in H))^((p not in A) and (p+1 in H)))}
        An={p for p in region if ((p-1 in A)^((p in A) or (p+1 in A)))}
        Bn={p for p in region if ((p-1 in B)^((p in B) or (p+1 in B)))}
        a,b,h=m(a),m(b),d(a,b,h);A,B,H=An,Bn,Hn
# Vacuum pulse inverse has a nonzero period-three tail at every tested depth.
for n in [3,6,32,257]:
    g=inverse(0,0,1,n)
    assert all(((g>>j)&1)==int(j%3!=2) for j in range(n))
assert m(3)!=d(0,0,3)  # Dropping subset invalidates physical recombination.
# The earlier forward/inverse probes store positive physical positions.
for x in range(256):
    initial={p for p in range(8) if x>>p&1}
    result={p for p in range(-1,9) if ((p-1 in initial)^((p in initial) or (p+1 in initial)))}
    packed=sum(1<<(p+1) for p in result)
    assert packed==((x<<2)^((x<<1)|x))
images=set()
for v in range(128):
    initial={p+1 for p in range(7) if v>>p&1}
    result={p for p in range(9) if ((p-1 in initial)^((p in initial) or (p+1 in initial)))}
    images.add(sum(1<<p for p in result))
tree=ast.parse((ROOT/'image_closure_probe.py').read_text(encoding='utf-8'))
only_function=ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='finite_preimage'],type_ignores=[])
namespace={};exec(compile(only_function,'finite_preimage','exec'),namespace)
for x in range(512):assert (namespace['finite_preimage'](x) is not None)==(x in images)
assert len(images)==128
out={'passed':True,'all_prefix_triples_checked':cases,'physical_recombination_controls':recombinations,
     'literal_physical_cells_checked':cells,'vacuum_inverse_period_three_controls':4,
     'positive_coordinate_pack_controls':256,'finite_image_membership_controls':512,
     'finite_only':True,'Lean_verified':False,'unbounded_subset_preservation_proved':False}
(ROOT/'independent-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
