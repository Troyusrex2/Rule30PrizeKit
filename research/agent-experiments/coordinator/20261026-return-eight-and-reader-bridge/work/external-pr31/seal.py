"""Create a new immutable audit delivery from exact sources and terminal evidence."""
from pathlib import Path
import datetime,hashlib,json,shutil
root=Path(__file__).resolve().parent;dest=root/'delivery-v01';assert not dest.exists()
source=json.loads((root/'public-source.json').read_bytes())
reports={key:json.loads((root/'formal'/key/'report.json').read_bytes()) for key in ['Rule30WhiteEndNine','Rule30PaddedWords']}
guards={p.stem:json.loads(p.read_bytes()) for p in (root/'evidence').glob('*.guard.json')}
assert len(guards)==16
assert sum(g['exit_code']==0 and g['guard_stop'] is None for g in guards.values())==15
assert guards['build_dependencies.guard']['guard_stop']=='wall_time'
assert all(r['passed'] and r['checker']['verdict']=='pass' and r['checker']['replay']['ok'] and not r['checker']['newAxioms'] and all(h['ok'] for h in r['checker']['headlines']) for r in reports.values())
integrity=json.loads((root/'final-environment-integrity.json').read_bytes());assert integrity['passed']
assert json.loads((root/'split-completion.json').read_bytes())['passed']
for module,item in source['sources'].items():
    assert hashlib.sha256((root/item['local_file']).read_bytes()).hexdigest()==item['sha256']
    assert reports[item['local_file'].removesuffix('.lean')]['source_sha256']==item['sha256']
audit={'verdict':'PASS','scope':'External PR31 exact-source review and full declaration replay of two updated modules, not own mathematical novelty or prize solution','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'upstream':source,'source_scope_review':'PASS','official_pin':source['official_pin'],'checker_sha256':reports['Rule30WhiteEndNine']['checker_sha256'],'formal':{k:{'passed':v['passed'],'declarations':v['checker']['replay']['constants'],'headline_count':len(v['checker']['headlines']),'new_axioms':v['checker']['newAxioms'],'compile_seconds':v['compile_seconds'],'replay_inclusive_seconds':v['total_seconds'],'guard':guards['replay-'+k+'.guard']} for k,v in reports.items()},'pumping_threshold':10,'kernel_base_case':9,'same_certificate_formula_for_all_q_ge9':True,'pumping_from_nine_negative_control_verified':True,'padded_bound_single_true':9,'official_dependencies':{'total':43,'copied_precompiled':16,'freshly_compiled':27,'aggregate_completed_before_timeout':14,'separate_successful_jobs':13},'attempts':{'guarded_jobs':16,'successful_jobs':15,'preserved_wall_timeout_jobs':1,'guard_limits':{'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2},'explanation':'The aggregate official dependency job hit 300 s after 14 successful compiles; remaining dependencies passed separate guarded compiles without source changes.'},'no_public_source_edits':True,'reference_write':False,'publication_performed':False,'all_owned_jobs_terminal':True,'not_verified':['Whole repository export/catalog build','Additional PR-body mixed-gap codebook/search claims','Any full prize theorem, ReturnComplete, D3, or ancestry completeness']}
(root/'AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n',encoding='utf-8')
brief='''# PR31 updated pumping proof: independent audit PASS

Exact external head: `88dd51194cc4ae48bff5339418d33b54265330cb` in AIOvernight/Rule30PrizeKit. This is external work by @AIOvernight/Claude; our contribution here is independent review and verification.

Both exact public source files passed full declaration replay using Lean 4.35.0, official pin5473, and unchanged Check.lean SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`:

| Module | Declarations | Headlines | Guarded total | Peak owned RSS |
| --- | ---: | ---: | ---: | ---: |
| Rule30WhiteEndNine | 204 | 8 | 4.47 seconds | 0.79 GiB |
| Rule30PaddedWords | 14 | 3 | 2.08 seconds | 0.75 GiB |

No new axioms, native decisions, checker edits, or public source edits. No semantic defect found. All jobs are terminal; the reference remained read-only.

The formula is uniform for every q >= 9, but the proof uses a separate kernel base case at q=9 and a general pumping theorem from q=10. The kernel also verifies that pumping from nine fails. The main module no longer imports Rule30WhiteEnd or a certificate-data module. The final exclusion range is the same as the previous PR revision; this revision improves its proof architecture. PaddedWords correctly lowers the single-tail bound from ten to nine and connects it to the existing short-tail theorem through word rotation.

One setup assumption failed because 27 official dependencies had no compiled artifacts in the reference. The first aggregate build completed 14 before its 300-second guard stopped it. All 13 remaining dependencies then passed individual guarded builds; the largest, WhitePaddingFamilies, took 174.39 seconds. This resource-limited attempt and the successful recovery are preserved. Source hashes for all 43 official dependencies and both public modules were rechecked after replay.

This establishes the stated eventual single-seed word exclusions and their padded-word wrapper. It is not a full prize solution, D3, ReturnComplete, or an arbitrary mixed-run exclusion. Additional search claims in the PR body were not adopted. The whole repository catalog/export build was not run; the two requested modules and their needed dependency graph were checked.

See SOURCE_REVIEW.md for the semantic review, REPLAY.md for exact commands and dependency handling, AUDIT.json for structured results, formal/ for raw checker output, evidence/ for guards, and MANIFEST.sha256 for the immutable bundle hashes. No GitHub publication or prize submission was performed by this reviewer.
'''
(root/'REPORT.md').write_text(brief,encoding='utf-8')
dest.mkdir()
names=['Rule30WhiteEndNine.lean','Rule30PaddedWords.lean','Check.lean','pr-metadata.json','changed-files.json','official-dependencies.json','public-source.json','overlay-receipt.json','environment.json','aggregate-completed-receipt.json','split-plan.json','split-completion.json','final-environment-integrity.json','attempts.json','padded-words-versus-official.diff','SOURCE_REVIEW.md','REPLAY.md','REPORT.md','AUDIT.json']
for p in root.glob('*.py'):names.append(p.name)
for name in names:shutil.copyfile(root/name,dest/name)
for name in ['formal','evidence','official-build','official-split']:shutil.copytree(root/name,dest/name)
entries={str(p.relative_to(dest)).replace('\\','/'):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(dest.rglob('*')) if p.is_file()}
manifest=''.join(f'{sha}  {path}\n' for path,sha in sorted(entries.items()))
(dest/'MANIFEST.sha256').write_text(manifest,encoding='utf-8')
assert all(hashlib.sha256((dest/path).read_bytes()).hexdigest()==sha for path,sha in entries.items())
print(json.dumps({'delivery':str(dest),'manifest_sha256':hashlib.sha256((dest/'MANIFEST.sha256').read_bytes()).hexdigest(),'hashed_files':len(entries),'verdict':'PASS','declarations':218}))
