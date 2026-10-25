"""Audit the independent classifications and hashes of the followup release."""
import hashlib,json
from core import HERE

def main():
    m=json.loads((HERE/'further-tests-artifacts.json').read_text(encoding='utf-8'))
    for name,sha in m['files'].items():assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==sha,name
    p=json.loads((HERE/'sparse-coupled-budget14-window7.json').read_text(encoding='utf-8'))
    assert p['maxima_complete'] and p['complete_extinction'] and p['last_complete_depth']==111
    assert all(r['zeros']<=3*r['black_evens'] for r in p['maximum_zeros_by_exact_even_cost'])
    assert not p['Lean_verified'] and not p['unbounded_charge_proved']
    for n in [48,64]:
        r=json.loads((HERE/f'coupled-charge-cnf-{n}-factor3-g4-seqcounter-prefixes.json').read_text(encoding='utf-8'))
        assert r['solver_status']=='unsat' and r['every_prefix_checked'] and r['controls']['all_passed']
        assert not r['Lean_verified'] and not r['unbounded_charge_proved']
    assert m['new_kernel_proofs']==0 and not m['full_problem_solved'] and not m['kernel_verified_all_prefix_bound']
    print({'followup_hash_and_claim_audit':'pass','files':len(m['files']),'new_kernel_proofs':0},flush=True)

if __name__=='__main__':main()
