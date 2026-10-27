from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
prior=['unusual-reader-20261026T2200/REPORT.md','clock-background-reader-20261026T2225/REPORT.md',
       'marker-frontier-20261026T2105/REPORT.md','orbit-quotient-20261026T0720/REPORT.md',
       'orbit-signalizer-catalog-candidate-20261026T2300/README.md',
       'external-0ef9c8-audit-20261027T0005/pinned/Rule30ControlledResponse.lean',
       'predecessor-periodicity-paper-20261026T2305/PAPER.md']
result={'status':'embedding candidate refuted; general acceleration OPEN',
        'new_lean_build':False,'new_kernel_claim':False,'new_census':False,
        'counterexample':'10 in S, E_3(10)=130 not in S; fails at D time8',
        'candidate_order_wqo':False,
        'regularity_of_S_refuted':False,
        'uniform_paper_facts':['K_N regular and depends only first4N+3 bits',
            'for everyN, finite-white torus truncation lies inK_N but notFix(D^2)',
            'existing terminal response expansions preserve S but have irreducible-word antichain'],
        'prior_sources':[{'path':s,'sha256':sha(p.parent/s)} for s in prior]}
(p/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
files=sorted(f for f in p.iterdir() if f.is_file() and not f.name.startswith('MANIFEST'))
manifest={'version':1,'files':[{'path':f.name,'bytes':f.stat().st_size,'sha256':sha(f)} for f in files]}
f=p/'MANIFEST-v1.json';f.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'paper_sha256':sha(p/'PAPER.md'),'manifest_sha256':sha(f),'files':len(files)}))
