from pathlib import Path
import hashlib,json
from mode_data import rotate
r=Path(__file__).resolve().parent
previous=r.parent/'mode-inverse-20261026T1216'
seed=r/'seed-original-collision.json'
if not seed.exists():seed=previous/'mode-genuine-local-inverse.json'
raw=seed.read_bytes();d=json.loads(raw)
reports=[]
for idx,x in enumerate(d['reports'][-1]['collision']):
    P=x['clock'];mask=(1<<P)-1
    dm=x['m']^rotate(x['m'],1,P)
    dn=x['n']^rotate(x['n'],1,P)
    bad=x['n']&~dm&mask
    required=dm&~x['n']&mask
    reports.append({'member':idx,'clock':P,'first_older_extension_exists':bad==0,
                    'bad_oldest_cell_times':[t for t in range(P) if bad>>t&1],
                    'second_older_extension_necessary_condition':(required&~dn)==0,
                    'conclusion':'inconsistent before imposing white boundary' if bad else 'further search needed'})
before_path=r/'public-feed-before.json'
if not before_path.exists():before_path=previous/'submissions.json'
after_path=r/'public-feed-at-start.json'
if not after_path.exists():after_path=r/'submissions.json'
before=json.loads(before_path.read_bytes())
after=json.loads(after_path.read_bytes())
b={x['id']:x for x in before['entries']};a={x['id']:x for x in after['entries']}
changes=[{'id':i,'changed_fields':sorted(k for k in a[i].keys()|b[i].keys() if a[i].get(k)!=b[i].get(k))}
         for i in sorted(a.keys()&b.keys()) if a[i]!=b[i]]
out={'previous_goal_turn':'progress','previous_authoritative_change':'two uniform full-kernel clock proofs and fork pushes',
     'seed_source_sha256':hashlib.sha256(raw).hexdigest(),'reports':reports,
     'global_boundary_necessity_not_established_by_these_seed_collisions':True,
     'public_submission_changes_since_1215':changes,'new_public_ids':sorted(a.keys()-b.keys()),
     'full_problem_solved':False}
(r/'seed-ancestry-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
