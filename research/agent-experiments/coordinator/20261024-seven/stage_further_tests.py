"""Publish a bounded-search followup without altering prior checked artifacts."""
import hashlib,json
from core import HERE,REPO

CNFS=[
 'coupled-charge-cnf-48-factor3-g4-seqcounter.json',
 'coupled-charge-cnf-48-factor3-g4-seqcounter-prefixes.json',
 'coupled-charge-cnf-64-factor3-g4-seqcounter-prefixes.json',
 'coupled-charge-cnf-96-factor3-g4-seqcounter.json',
 'coupled-charge-cnf-96-factor3-g4-seqcounter-prefixes.json',
 'coupled-charge-cnf-96-factor3-m22-seqcounter-prefixes.json',
 'coupled-charge-cnf-96-factor3-g4-totalizer.json']

def main():
    dest=REPO/'research/agent-experiments/coordinator/20261024-seven'
    old=json.loads((dest/'language-budget-artifacts.json').read_text(encoding='utf-8'))
    for name,sha in old['files'].items():assert hashlib.sha256((dest/name).read_bytes()).hexdigest()==sha
    table=['\n## CNF result table\n\n| Length | Engine | Query | Encoding | Result | Seconds |\n',
      '| ---: | --- | --- | --- | --- | ---: |\n']
    for name in CNFS:
        r=json.loads((HERE/name).read_text(encoding='utf-8'))
        assert r['solver_status']!='sat','Actual charge counterexample: revise the report before release'
        assert r['controls']['all_passed'] and not r['Lean_verified'] and not r['unbounded_charge_proved']
        query='every prefix' if r.get('every_prefix_checked') else 'final length'
        enc='exact unary prefix counter' if r.get('every_prefix_checked') else r['encoding']
        table.append(f"| {r['length']} | {r['engine']} | {query} | {enc} | {r['solver_status']} | {r['seconds']} |\n")
    report=(HERE/'FURTHER-TESTS.md').read_text(encoding='utf-8').split('\n## CNF result table')[0]
    (HERE/'FURTHER-TESTS.md').write_text(report+''.join(table),encoding='utf-8',newline='\n')
    names=CNFS+['FURTHER-TESTS.md','stage_further_tests.py','audit_further_tests.py',
      'sparse_coupled_charge.py','sparse-coupled-budget12-window7.json','sparse-coupled-budget14-window7.json',
      'sparse-coupled-budget12-window30.json','sparse-coupled-budget24-window30.json','sparse-coupled-budget48-window30.json',
      'charge-coupled-factor3-image7-2048.json','charge-coupled-factor3-image7.json',
      'right-free-language-7.json','right-image-smt-7.json','right-language-automaton-7.json',
      'right_image_graph.py','right-image-graph-30.json','coupled_semidefinite_rank.py',
      'coupled-semidefinite-rank.json','coupled-semidefinite-rank-homogeneous.json',
      'coupled_neural_rank.py','coupled-neural-rank.json','periodic_charge_probe.py','periodic-charge-seven-period14.json',
      'coupled_charge_cnf.py','language_charge_cnf.py','language-charge-cnf-96-guard7-g4.json',
      'power_time_probe.py','power-time-probe.json','joint_gap_profile.py','joint-gap-profile-30.json']
    records={}
    for name in names:
        raw=(HERE/name).read_bytes().replace(b'\r\n',b'\n');target=dest/name
        if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different prior artifact: '+name)
        target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw);records[name]=hashlib.sha256(raw).hexdigest()
    result={'prerequisite_checked_commit':'c141fc9b515b8bd49b806f11bb0cb18d693d37bc',
        'files':records,'new_kernel_proofs':0,'full_problem_solved':False,'unbounded_charge_proved':False,
        'largest_all_prefix_CNF_UNSAT':64,'kernel_verified_all_prefix_bound':False,
        'guard_limits':{'seconds':300,'rss_gib':8,'minimum_free_gib':2}}
    payload=json.dumps(result,indent=2)+'\n'
    (HERE/'further-tests-artifacts.json').write_text(payload,encoding='utf-8',newline='\n')
    (dest/'further-tests-artifacts.json').write_text(payload,encoding='utf-8',newline='\n')
    print({'followup_files':len(records),'prior_checked_release_unchanged':True,'full_problem_solved':False},flush=True)

if __name__=='__main__':main()
