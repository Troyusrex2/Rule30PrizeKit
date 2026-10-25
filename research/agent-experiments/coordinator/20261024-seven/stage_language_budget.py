"""Stage only exact replayed sources and explicitly selected research data."""
import hashlib,json
from core import HERE,REPO
from verification_context import PIN

def items():
    pairs=[('Rule30GoldenBudgetResearch','golden-budget-evidence'),
      ('Rule30GoldenBudgetDFSResearch','golden-budget-dfs-evidence'),
      ('Rule30GoldenBudgetPilotResearch','golden-budget-pilot-evidence'),
      ('Rule30GoldenBudgetDFSPilotResearch','golden-budget-dfs-pilot-evidence'),
      ('Rule30GoldenBudgetSmokeResearch','golden-budget-smoke-evidence'),
      ('Rule30GoldenPackedBitsResearch','golden-packed-bits-evidence'),
      ('Rule30GoldenPackedBudgetResearch','golden-packed-budget-evidence'),
      ('Rule30GoldenPackedSmokeResearch','golden-packed-smoke-evidence'),
      ('Rule30GoldenCompactCodecResearch','golden-compact-codec-evidence'),
      ('Rule30GoldenCompactBudgetResearch','golden-compact-budget-evidence'),
      ('Rule30GoldenCompactSmokeResearch','golden-compact-smoke-evidence')]
    pairs += [(f'Rule30GoldenBudgetDAG4Part{i:04d}Research',f'golden-budget4-dag-evidence/Rule30GoldenBudgetDAG4Part{i:04d}Research') for i in range(6)]
    pairs += [('Rule30GoldenBudgetDAG4Research','golden-budget4-dag-evidence/Rule30GoldenBudgetDAG4Research'),
      ('Rule30GoldenBudgetCoupledResearch','golden-budget-coupled-evidence'),
      ('Rule30CoupledChargeReductionResearch','coupled-charge-reduction-evidence'),
      ('Rule30CoupledSixWordResearch','coupled-six-word-evidence'),
      ('Rule30CoupledWordCertificateResearch','coupled-word-certificate-evidence'),
      ('Rule30CoupledSevenWordResearch','coupled-seven-word-evidence'),
      ('Rule30ExternalThreeFifthsAudit','external/0554f7-evidence')]
    return pairs

def main():
    dest=REPO/'research/agent-experiments/coordinator/20261024-seven';files=set();modules=[];checker=None
    for module,folder in items():
        source=module+'.lean';report=folder+'/report.json';r=json.loads((HERE/report).read_text(encoding='utf-8'))
        sha=hashlib.sha256((HERE/source).read_bytes()).hexdigest();ck=r['check']
        assert sha==r['source_sha256'] and r['kit_commit']==PIN and r['checker_unchanged']
        assert ck['verdict']=='pass' and ck['replay']['ok'] and not ck['newAxioms'] and all(h['ok'] for h in ck['headlines'])
        if checker is None:checker=r['checker_sha256']
        assert checker==r['checker_sha256']
        modules.append({'module':module,'source_sha256':sha,'report':report,'constants':ck['replay']['constants'],
            'headlines':[h['name'] for h in ck['headlines']],'attributed':module=='Rule30ExternalThreeFifthsAudit'})
        files.update([source,report])
        if (HERE/folder/'resources.json').exists():files.add(folder+'/resources.json')
    original=json.loads((HERE/'submissions-20261025T011607Z.json').read_text(encoding='utf-8'))
    entry=next(e for e in original['entries'] if e['id']=='R30-20261025-0554f7')
    provenance={k:entry[k] for k in ['id','title','authors','status','tags','page','files']}
    provenance.update({'retrieved_catalog_updated':original['updated'],'source_sha256':modules[-1]['source_sha256'],
        'local_full_replay_constants':143,'not_our_result':True})
    (HERE/'external/0554f7-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n',encoding='utf-8',newline='\n')
    status={'budget8_kernel_certificate_completed':False,'uniform_budget_termination_proved':False,
        'full_problem_solved':False,'guard':{'seconds':300,'rss_gib':8,'minimum_free_gib':2},
        'failed_large_probe_representations':['list state','packed R/Rm with separate flags','whole-state integer'],
        'explicit_state_DAG4':'717 live states, six checked parts, checked root, all pass',
        'numerical_budget8_and10_extinction':'not a kernel proof; no unbounded conclusion',
        'invalid_initial_state_prototype':'excluded; none of its data are published here'}
    (HERE/'language-budget-search-status.json').write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8',newline='\n')
    files.update(['COUPLED-LANGUAGE.md','stage_language_budget.py','replay_language_budget.py',
      'build_golden_budget_dag.py','trace_verify.py','golden-budget4-dag-plan.json',
      'language-budget-search-status.json','external/0554f7-provenance.json',
      'sparse_even_prefix_tree.py','sparse-even-prefix-budget8.json','sparse-even-prefix-budget10.json',
      'sparse-even-prefix-budget12.json',
      'golden-packed-leaf-probe-evidence/resources.json','golden-compact-leaf-probe-evidence/resources.json',
      'zero_tail_block_rank.py','zero-tail-block-rank.json','zero-tail-block-rank-parity.json',
      'zero-tail-block-rank-six.json','zero-tail-block-rank-six-parity.json','zero-tail-block-rank-seven-parity.json',
      'zero_tail_gap_search.py','zero-tail-gap-search-128.json','right_free_language.py',
      'right-free-language-12.json','right-free-language-14.json','right_image_smt.py',
      'right-image-smt-12.json','right-image-smt-20.json','right-image-smt-20-sat.json','right-image-smt-30.json',
      'right_language_automaton.py','right-language-automaton-20.json','analyze_right_image.py','right-image-analysis-30.json',
      'charge_coupled_beam.py','charge-coupled-factor2-image0.json','charge-coupled-factor2-image14.json',
      'charge-coupled-factor3-image0.json','charge-coupled-factor3-image14.json',
      'coupled_charge_query.py','coupled-charge-query-48-factor3.json'])
    files.update(['coupled-charge-query-48-factor3-prefixes.json','coupled-charge-query-12-factor2-prefixes.json'])
    if (HERE/'coupled-charge-query-96-factor3.json').exists():files.add('coupled-charge-query-96-factor3.json')
    records={}
    for name in sorted(files):
        raw=(HERE/name).read_bytes().replace(b'\r\n',b'\n');target=dest/name;target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists() and target.read_bytes()!=raw:raise RuntimeError('Different already-public artifact: '+name)
        target.write_bytes(raw);records[name]=hashlib.sha256(raw).hexdigest()
    for m in modules:assert records[m['module']+'.lean']==m['source_sha256']
    manifest={'kit_commit':PIN,'checker_sha256':checker,'files':records,'modules':modules,
      'owned_replayed_constants':sum(m['constants'] for m in modules if not m['attributed']),
      'attributed_replayed_constants':sum(m['constants'] for m in modules if m['attributed']),
      'full_problem_solved':False,'unbounded_charge_proved':False,'uniform_budget_termination_proved':False}
    payload=json.dumps(manifest,indent=2)+'\n';(HERE/'language-budget-artifacts.json').write_text(payload,encoding='utf-8',newline='\n')
    (dest/'language-budget-artifacts.json').write_text(payload,encoding='utf-8',newline='\n')
    print({'modules':len(modules),'files':len(files),'owned_constants':manifest['owned_replayed_constants'],
        'attributed_constants':manifest['attributed_replayed_constants']},flush=True)

if __name__=='__main__':main()
