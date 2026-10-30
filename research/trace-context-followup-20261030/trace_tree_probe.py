import json
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
start = time.monotonic()
n = 16


def encode(a, right):
    row = (a << 1) | right
    sig = 0
    for t in range(n):
        sig |= ((row >> (1+t)) & 1) << t
        row ^= (row << 1) | (row << 2)
    return sig


def literal_encode(a, right, bits):
    black = {-i for i in range(a.bit_length()) if a >> i & 1}
    if right:
        black.add(1)
    sig = 0
    for t in range(bits):
        sig |= int(0 in black) << t
        if black:
            black = {p for p in range(min(black)-1,max(black)+2)
                     if ((p-1 in black) ^ ((p in black) or (p+1 in black)))}
    return sig


e0 = [encode(a, 0) for a in range(1 << n)]
e1 = [encode(a, 1) for a in range(1 << n)]
assert len(set(e0)) == len(set(e1)) == 1 << n
for right, enc in enumerate([e0,e1]):
    for a in range(256):
        assert enc[a] & 255 == literal_encode(a,right,8)
    for k in range(128):
        a = k*40503 % (1 << n)
        assert enc[a] == literal_encode(a,right,n)
    for depth in range(n+1):
        mask = (1 << depth)-1
        assert all(enc[a] & mask == enc[a & mask] & mask for a in range(1 << n))
inv1 = [0]*(1 << n)
for a, e in enumerate(e1):
    inv1[e] = a
change = [inv1[e] for e in e0]
assert len(set(change)) == 1 << n
counts = []
for d in range(9):
    sections = {}
    for prefix in range(1 << d):
        fp = tuple((change[prefix+(suffix << d)] >> d) & 255 for suffix in range(256))
        sections.setdefault(fp, prefix)
    counts.append(dict(prefix_depth=d, distinct_sections=len(sections),
                       suffix_bits=8, prefix_representatives=list(sections.values())))
    assert time.monotonic()-start < 30
small_pairs = [[a,change[a]] for a in range(32)]
out = dict(status='exact_finite_section_lower_bounds_only',
           encoder_permutations_verified=True, section_counts=counts,
           encoder_prefix_compatibility_all_depths_verified=True,
           independent_literal_controls={'all_8_bit_inputs_both_contexts':512,
                                         'deterministic_16_bit_inputs_both_contexts':256},
           excludes_at_most_16_state_mealy=max(v['distinct_sections'] for v in counts)>16,
           low_integer_inputs_and_output_prefixes=small_pairs,
           prefix_bits=n, seconds=time.monotonic()-start,
           no_eventual_zero_or_infinite_trace_classification_claim=True)
(ROOT/'trace-tree-result.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=out['status'],
                      section_counts=[v['distinct_sections'] for v in counts],
                      independent_literal_controls=out['independent_literal_controls'],
                      seconds=out['seconds'])))
