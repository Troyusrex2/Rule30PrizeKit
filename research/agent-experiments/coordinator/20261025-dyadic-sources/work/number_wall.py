from pathlib import Path
from itertools import product
from collections import Counter
import hashlib, json, random, time
from wall_tools import center, physical_center, bm, det, det_leibniz, leading, wall

root = Path(__file__).resolve().parent
start = time.monotonic()
rng = random.Random(300025)
controls = {'exhaustive_bm_determinants':0,'leibniz':0,'physical_steps':0,
            'direct_wall_determinants':0,'jacobi_identities':0}
for word in product(range(2),repeat=10):
    ds = leading(word)
    for n in range(1,6):
        assert ds[n] == det(word,n)
        controls['exhaustive_bm_determinants'] += 1
        if n <= 4:
            assert ds[n] == det_leibniz(word,n)
            controls['leibniz'] += 1
for rule in [30,90,150,210]:
    assert center(rule,128) == physical_center(rule,128)
    controls['physical_steps'] += 128

N = 65536
raw = center(30,N)
(root/'center-65536.bin').write_bytes(bytes(raw))
streams = {f'rule{r}': (raw if r==30 else center(r,N)) for r in [30,90,150,210]}
streams.update({'rule30_source':[x^1 for x in raw],
                'thue_morse':[n.bit_count() & 1 for n in range(N)],
                'periodic_001011':[0,0,1,0,1,1]*(N//6)+[0,0,1,0,1,1][:N%6],
                'random':[rng.randrange(2) for _ in range(N)]})
out = {'claim':'finite diagnostics only; no new proof','controls':controls,'sequences':{}}
for name, bits in streams.items():
    print('working',name,flush=True)
    ds = leading(bits)
    # Equal downsampled prefixes at each depth are only finite-kernel statistics.
    kernel = {}
    for k in range(9):
        q=1<<k; length=64
        fingerprints = {bytes(ds[r:r+q*length:q]) for r in range(q)}
        kernel[str(k)] = len(fingerprints)
    profiles = []
    for end in [64,256,1024,4096,16384,32768]:
        zero = best = 0
        for value in ds[1:end+1]:
            zero = zero+1 if value == 0 else 0
            best=max(best,zero)
        profiles.append({'through_n':end,'ones':sum(ds[1:end+1]),'longest_zero_run':best})
    w = wall(bits,128,258)
    # Direct elimination checks all small n and random larger n, independently of BM.
    for n,t in [(n,t) for n in range(17) for t in range(24)] + [(rng.randrange(1,129),rng.randrange(258)) for _ in range(128)]:
        assert w[n][t] == det(bits,n,t)
        controls['direct_wall_determinants'] += 1
    for n in range(2,129):
        for t in range(256):
            assert (w[n][t]*w[n-2][t+2]) == ((w[n-1][t]*w[n-1][t+2]) ^ w[n-1][t+1])
            controls['jacobi_identities'] += 1
    fine = {}
    for e,f in product(range(2),repeat=2):
        table={}; witnesses=[]; train_conflicts=0
        for n in range(2,32):
            for t in range(2,128):
                key=tuple(w[n+u][t+v] for u,v in product(range(-1,2),repeat=2))
                value=w[2*n+e][2*t+f]
                if key in table and table[key][0] != value:
                    train_conflicts += 1
                    if len(witnesses)<2:
                        witnesses.append({'coarse_patch':list(key),'old':table[key],
                                          'new':[value,n,t]})
                else:
                    table[key]=(value,n,t)
        held_errors=unseen=0
        for n in range(32,64):
            for t in range(2,128):
                key=tuple(w[n+u][t+v] for u,v in product(range(-1,2),repeat=2))
                if key not in table: unseen+=1
                elif table[key][0] != w[2*n+e][2*t+f]: held_errors+=1
        fine[f'{e},{f}']={'training_conflicts':train_conflicts,'distinct_coarse_patches':len(table),
                         'held_seen_errors':held_errors,'held_unseen':unseen,'witnesses':witnesses}
    result={'leading_profile':profiles,'finite_leading_kernel_prefix64':kernel,
            'dyadic_leading':{str(k):ds[1<<k] for k in range(16)},
            'coarse_patch_prediction':fine,'leading_sha256':hashlib.sha256(bytes(ds)).hexdigest()}
    out['sequences'][name]=result
    (root/(name+'-leading.bin')).write_bytes(bytes(ds))
    if name.startswith('rule30'):
        (root/(name+'-wall.bin')).write_bytes(bytes(x for row in w for x in row))
    print(name,'leading kernel',kernel,'dyadic',result['dyadic_leading'],flush=True)
out['elapsed_seconds']=time.monotonic()-start
out['center_sha256']=hashlib.sha256(bytes(raw)).hexdigest()
(root/'number-wall.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'controls':controls,'elapsed_seconds':out['elapsed_seconds']}))
