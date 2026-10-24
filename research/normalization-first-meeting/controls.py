"""Independent finite controls, not a substitute for the all-size Lean proof."""
import json
from pathlib import Path
import random
import re
import time

HERE = Path(__file__).resolve().parent

def phi(a):
    return a ^ ((a << 1) | (a << 2))

def scalar_phi(a):
    # Lookup by (left, center, right), with bit zero physically on the right.
    table = (0,1,1,1,1,0,0,0)
    out = 0
    for i in range(a.bit_length()+2):
        left = (a >> i) & 1
        center = (a >> (i-1)) & 1 if i >= 1 else 0
        right = (a >> (i-2)) & 1 if i >= 2 else 0
        out |= table[4*left+2*center+right] << i
    return out

def stripe_regex(a,n):
    return re.fullmatch(r'0*(?:1|11)(?:01)*',
                        ''.join(str((a >> i) & 1) for i in range(n))) is not None

def stripe_dfa(a,n):
    transition = ((0,1),(2,3),(4,3),(2,4),(4,4))
    state = 0
    for i in range(n):
        state = transition[state][(a >> i) & 1]
    return state in (1,3)

def related(a,b,c):
    if a == b:
        return True
    for j in range(c+1):
        if (stripe_regex(a,j+1) and stripe_regex(b,j+1)
                and ((a >> j) & 1) and ((b >> j) & 1)
                and not ((a >> (j+1)) & 1) and not ((b >> (j+1)) & 1)
                and (a >> (j+2)) == (b >> (j+2))):
            return True
    return False

def numerical_normalizer(a,c):
    # Historical integer recurrence; independent of the regex and parser.
    # Its equality kernel has not yet been identified with StripeRelated in Lean.
    if not a:
        return 0
    low = (a & -a).bit_length()-1
    pattern = 1 << low
    out = a
    for j in range(low,min(c,a.bit_length()-1)+1):
        if j > low:
            pattern = (pattern << 1) + (1 if (j-low)%2 else -1)*(1 << low)
        if a & ((1 << (j+1))-1) == pattern and not (a >> (j+1)) & 1:
            out = (a >> j) << j
    return out

def main():
    started = time.monotonic()
    grammar = 0
    for n in range(13):
        for a in range(1 << n):
            assert stripe_regex(a,n) == stripe_dfa(a,n),(a,n)
            grammar += 1
    rng = random.Random(30301024)
    scalar = 0
    for _ in range(3000):
        a = rng.getrandbits(rng.randrange(129))
        for _ in range(3):
            assert phi(a) == scalar_phi(a),a
            a = phi(a)
            scalar += 1
    comparisons = guards = preservation = 0
    for a in range(64):
        for b in range(64):
            for c in range(7):
                initially_related = related(a,b,c)
                assert initially_related == (numerical_normalizer(a,c)==numerical_normalizer(b,c)),(a,b,c)
                comparisons += 1
                a1,b1 = phi(a),phi(b)
                if initially_related:
                    assert ((a >> c) & 1)==((b >> c) & 1),(a,b,c)
                    assert ((a1 >> (c+1)) & 1)==((b1 >> (c+1)) & 1),(a,b,c)
                    assert related(phi(a1),phi(b1),c+2),(a,b,c)
                    preservation += 1
                if (((a >> c) & 1)==((b >> c) & 1)
                        and ((a1 >> (c+1)) & 1)==((b1 >> (c+1)) & 1)):
                    assert (not related(phi(a1),phi(b1),c+2)
                            or related(a,b,c) or related(a1,b1,c+1)),(a,b,c)
                    guards += 1
    random_comparisons = 0
    for _ in range(2000):
        a = rng.getrandbits(rng.randrange(65))
        b = rng.getrandbits(rng.randrange(65))
        c = rng.randrange(70)
        for t in range(3):
            assert related(a,b,c+t) == (numerical_normalizer(a,c+t)==numerical_normalizer(b,c+t)),(a,b,c,t)
            a,b = phi(a),phi(b)
            random_comparisons += 1
    observed_steps = preserved_trace_steps = 0
    for a in range(32):
        for b in range(32):
            for c in range(6):
                x,y = a,b
                early = related(a,b,c) or related(phi(a),phi(b),c+1)
                initially_related = related(a,b,c)
                for t in range(16):
                    assert not related(x,y,c+t) or early,(a,b,c,t)
                    observed_steps += 1
                    if initially_related:
                        assert ((x >> (c+t)) & 1) == ((y >> (c+t)) & 1),(a,b,c,t)
                        preserved_trace_steps += 1
                    if ((x >> (c+t)) & 1) != ((y >> (c+t)) & 1):
                        break
                    x,y = phi(x),phi(y)
    x,y = 2,3
    norms = []
    for t in range(3):
        norms.append([numerical_normalizer(x,1+t),numerical_normalizer(y,1+t)])
        x,y = phi(x),phi(y)
    assert norms == [[2,2],[14,13],[50,50]]
    report = {'verdict':'pass','finite_controls_only':True,
              'grammar_words':grammar,'independent_scalar_rule30_steps':scalar,
              'exhaustive_relation_normalizer_comparisons':comparisons,
              'two_step_trace_guard_cases':guards,
              'two_step_preservation_cases':preservation,
              'preserved_center_trace_observations':preserved_trace_steps,
              'random_relation_normalizer_comparisons':random_comparisons,
              'finite_early_meeting_observations':observed_steps,
              'non_equivariance_counterexample':{'rows':[2,3],'center_index':1,'normalizations':norms},
              'numeric_normalizer_equivalence_proved':False,
              'infinite_trace_completeness_proved':False,'full_problem_solved':False,
              'seconds':round(time.monotonic()-started,3)}
    (HERE/'controls-report.json').write_text(json.dumps(report,indent=2)+'\n',
                                           encoding='utf-8',newline='\n')
    print(json.dumps(report))

if __name__=='__main__':
    main()
