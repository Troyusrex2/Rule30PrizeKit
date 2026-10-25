"""Analyze a complete finite census without inferring an infinite law."""
import json
from core import HERE,save
from right_image_smt import encode

def main():
    ref=json.loads((HERE/'right-image-smt-30.json').read_text(encoding='utf-8'))
    assert ref['finite_census_complete'];image={int(w):u for w,u in ref['image_witnesses'].items()}
    counts={str(k):len({w&((1<<k)-1) for w in image}) for k in range(1,31)}
    mins={str(k):10**6 for k in range(1,31)};worst=None
    for w,R in image.items():
        f=[w>>j&1 for j in range(30)];E=encode(f);score=0
        for j,s in enumerate(f):
            score+=3*(E>>j&1)-(1-s);mins[str(j+1)]=min(mins[str(j+1)],score)
            if worst is None or score<worst['deficit']:
                worst={'length':j+1,'deficit':score,'free_prefix_hex':hex(w&((1<<(j+1))-1)),
                    'right_initial_witness_hex':hex(R),'even_input_hex':hex(E&((1<<(j+1))-1))}
    for n in [12,14,20]:
        path=HERE/f'right-free-language-{n}.json' if n!=20 else HERE/'right-image-smt-20.json'
        r=json.loads(path.read_text(encoding='utf-8'))
        assert counts[str(n)]==r.get('image_words',r.get('image_word_count'))
    out={'complete_finite_image_length':30,'image_counts':counts,'minimum_factor3_deficit_by_prefix':mins,
        'all_prefixes_through30_satisfy_factor3_numerically':all(v>=0 for v in mins.values()),
        'worst_prefix_witness':worst,'independent_shorter_censuses_agree':True,
        'Lean_verified':False,'infinite_growth_law_proved':False,'unbounded_charge_proved':False,'full_problem_solved':False}
    save('right-image-analysis-30.json',out);print(out,flush=True)

if __name__=='__main__':main()
