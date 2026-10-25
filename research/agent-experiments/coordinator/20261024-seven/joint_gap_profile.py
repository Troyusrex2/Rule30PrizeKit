"""Test a simpler per-black-input charging rule against the actual census."""
import json
from core import HERE,save
from right_image_smt import encode

r=json.loads((HERE/'right-image-smt-30.json').read_text(encoding='utf-8'));assert r['finite_census_complete']
best={'zeros_since_last_black':-1};gapbest={'zero_even_gap':-1}
for w,R in ((int(w),R) for w,R in r['image_witnesses'].items()):
    f=[w>>j&1 for j in range(30)];E=encode(f);z=gap=0;last=-1
    for j,s in enumerate(f):
        if E>>j&1:z=0;gap=0;last=j
        else:gap+=1
        z+=1-s
        if z>best['zeros_since_last_black']:
            best={'zeros_since_last_black':z,'prefix_length':j+1,'last_black_index':last,
                'right_initial_hex':hex(R),'free_word_hex':hex(w),'even_input_hex':hex(E)}
        if gap>gapbest['zero_even_gap']:
            gapbest={'zero_even_gap':gap,'prefix_length':j+1,'right_initial_hex':hex(R),
                'free_word_hex':hex(w),'even_input_hex':hex(E)}
out={'census_length':30,'words_checked':len(r['image_witnesses']),'best_charge_segment':best,
     'longest_observed_zero_even_gap':gapbest,'segment_capacity_three_holds_in_census':best['zeros_since_last_black']<=3,
     'Lean_verified':False,'uniform_segment_capacity_proved':False,'full_problem_solved':False}
save('joint-gap-profile-30.json',out);print(out,flush=True)
