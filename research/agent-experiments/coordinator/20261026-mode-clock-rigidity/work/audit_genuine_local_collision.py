"""Independent literal audit of the genuine-plateau finite-strip collision."""
from pathlib import Path
import hashlib,json
r=Path(__file__).resolve().parent
raw=(r/'mode-genuine-local-inverse.json').read_bytes();data=json.loads(raw)
collision=data['reports'][-1]['collision'];assert collision is not None
P=collision[0]['clock'];R=collision[0]['R'];T=2*P
profiles=[]
for item in collision:
    rows=[[item[key]>>(t%(T if key in ['g','h'] else P))&1
           for key in ['n','m','l','k','h','g']] for t in range(T)]
    for t,field in enumerate(rows):
        for j in range(2,6):
            expected=(30>>(4*field[j]+2*field[j-1]+field[j-2]))&1
            assert rows[(t+1)%T][j]==expected
        assert rows[(t+P)%T][4]==1-field[4]
        assert rows[(t+R)%T][3]==1-field[3]
        assert rows[(t+R)%T][2]==field[2]
    q=[rows[t+P][5]^rows[t][5] for t in range(P)]
    rho=[(rows[t+P][5]|rows[t+P][4])^(rows[t][5]|rows[t][4]) for t in range(P)]
    S=[1^rho[(t+1)%P]^rho[t] for t in range(P)]
    assert sum(b<<t for t,b in enumerate(q))==item['q']
    assert sum(b<<t for t,b in enumerate(S))==item['S']
    profiles.append((q,S,rows))
assert profiles[0][1]==profiles[1][1]
shift=next(t for t in range(P) if profiles[0][0][t]!=profiles[1][0][t])
rotated=[]
for q,S,rows in profiles:
    rotated.append({'rows_oldest_to_newest':rows[shift:]+rows[:shift],
                    'q':[q[(t+shift)%P] for t in range(P)],
                    'S':[S[(t+shift)%P] for t in range(P)]})
assert rotated[0]['q'][0]!=rotated[1]['q'][0] and rotated[0]['S']==rotated[1]['S']
out={'passed':True,'clock':P,'driver_half_clock':R,'period':T,
     'source_sha256':hashlib.sha256(raw).hexdigest(),'shift_for_target_bit_collision':shift,
     'rotated_witnesses':rotated,'literal_Rule30_checked_from_index':2,
     'oldest_two_cells_arbitrary':True,'finite_white_ancestry_established':False,
     'refutes_only_ancestry_free_local_mode_inverse':True,'uniform_actual_observer_refuted':False,
     'Lean_verified':False,'full_problem_solved':False}
(r/'genuine-local-collision-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rotated_witnesses'}))
