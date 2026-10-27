from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
input_path = ROOT / 'INVERSE-RESULT.json'
candidate = json.loads(input_path.read_text(encoding='utf-8'))['candidate']
k = candidate['clock']
cycle = candidate['cycle']
j = candidate['pair_index']
n = len(cycle)
assert (k, n, candidate['global_period'], candidate['column_period']) == (6, 84, 6, 2)
profiles = [cycle[(j-i) % n] >> k for i in range(n)]
assert profiles[:2] == [42, 44]
rows = [sum(((profiles[i] >> t) & 1) << i for i in range(n)) for t in range(k)]

# Independent direct PHYSICAL rows, without the backward pair-map code.
def evolve_row(row):
    out = 0
    for i in range(n):
        l = (row >> ((i-1) % n)) & 1
        c = (row >> i) & 1
        r = (row >> ((i+1) % n)) & 1
        out |= (l ^ (c | r)) << i
    return out

assert all(evolve_row(rows[t]) == rows[(t+1) % k] for t in range(k))
assert len(set(rows)) == 6
center = [p & 1 for p in rows]
right = [(p >> 1) & 1 for p in rows]
assert center == [0,1,0,1,0,1]
assert right == [0,0,1,1,0,1]
assert all(center[t] == center[(t+2) % k] for t in range(k))
assert right[1] != right[5]

forward = [right[t] ^ right[(t+4) % k] for t in range(k)]
backward = [right[t] ^ right[(t-4) % k] for t in range(k)]
assert forward == [0,1,1,1,1,0]
assert backward == [1,1,1,0,0,1]
forward_births = [t for t in range(k) if not forward[t] and forward[(t+1) % k]]
backward_births = [t for t in range(k) if not backward[t] and backward[(t+1) % k]]
assert forward_births == [0]
assert backward_births == [4]

# Check exact physical birth event at its source phase: both compared
# column-one values are white and column-two values differ.
two = [(p >> 2) & 1 for p in rows]
assert right[4] == right[0] == 0 and two[4] != two[0]

out = dict(status='PASS_SCALAR_NOT_KERNEL', temporal_period=6, spatial_period=84,
           center_least_period=2, right_least_period=6, profiles_physical_order=profiles,
           rows_base10=[str(r) for r in rows], center=center, right=right,
           forward_shift4_mismatch=forward, backward_shift4_mismatch=backward,
           forward_birth_phases=forward_births, backward_birth_phases=backward_births,
           periodic_scalar_stencils_checked=n*k,
           infinity_scope='Lift residues modulo84 to every integer physical position',
           finite_support=False,
           inverse_result_sha256=hashlib.sha256(input_path.read_bytes()).hexdigest(),
           audit_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(ROOT/'PHYSICAL-AUDIT.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({a:b for a,b in out.items() if a not in ('profiles_physical_order','rows_base10')}))
