"""Cross-check the retained proof evidence and the independent Cedar certificate."""
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
cedar=Path('D:/MWB/Rule30/agent-inbox/r30-codex-cedar-followup-20261026T154236Z-b768c9a6-v02')
mods={'CedarSafetySoundness':137,'CedarSafetySemantics':75,'CedarSafetyBridge':8,'RootShortExtensionCore':36,'RootShortExtensionCases':232,'RootShortExtensionCertificate':1,'RootShortExtension':4}
dependency=[];results=[]
for module,count in mods.items():
    raw=(root/(module+'.lean')).read_bytes();digest=hashlib.sha256(raw).hexdigest()
    report=json.loads((root/'formal'/module/'report.json').read_bytes());check=report['checker']
    assert report['passed'] and report['source_sha256']==digest
    assert report['pin']=='5473ffd075f63c9d626e63b8455805d4831b39ca'
    assert report['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert check['verdict']=='pass' and check['replay']=={'constants':count,'ok':True}
    assert check['claim']=='partial' and check['importsStatements'] and not check['newAxioms'] and not check['verifiedTargets']
    assert all(h['ok'] and h['typeMatches'] for h in check['headlines'])
    guard=json.loads((root/'evidence'/('replay-'+module+'.guard.json')).read_bytes())
    assert guard['exit_code']==0 and guard['guard_stop'] is None
    assert guard['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
    assert guard['elapsed_seconds']<300 and guard['peak_owned_rss_bytes']<8*1024**3 and guard['minimum_system_available_bytes']>=2*1024**3
    results.append({'module':module,'source_sha256':digest,'constants':count,'guarded_seconds':guard['elapsed_seconds'],'peak_owned_rss_bytes':guard['peak_owned_rss_bytes']})
    if module.startswith('Cedar'):
        original=cedar/'verifier'/(module+'.lean');assert original.read_bytes()==raw
        dependency.append({'module':module,'original_response':'r30-codex-cedar-followup-20261026T154236Z-b768c9a6-v02','original_path':'verifier/'+module+'.lean','sha256':digest,'fresh_replay':True})
states={int(i):(int(q),int(p),int(r)) for i,q,p,r in re.findall(r'\| (\d+) => ⟨(\d+), ofNat (\d+), ofNat (\d+)⟩',(root/'CedarSafetySoundness.lean').read_text(encoding='utf-8'))}
old=json.loads((cedar/'structural/safe-short-extensions.json').read_bytes())
profiles=json.loads((cedar/'structural/eight-profile-bridge.json').read_bytes())
lookup={}
for row in old['cases']:
    pair=profiles['profile_states'][row['prefix_profile_state']]
    key=(pair[1]&255,pair[0]&255,tuple(row['append']))
    assert key not in lookup;lookup[key]=row
new=json.loads((root/'generated-cases.json').read_bytes())
matched=0
for row in new['cases']:
    if not row['word']:continue
    q,p,r=states[row['state']]
    oldrow=lookup[(p&255,r&255,tuple(row['word']))]
    assert row['return8']==oldrow['whole_word_return8']
    if not row['return8']:assert not oldrow['safe'] and row['unsafe_pair_start'] is not None
    matched+=1
assert matched==210 and new['total_cases_including_empty']==225
(root/'dependencies.json').write_text(json.dumps({'pin':'5473ffd075f63c9d626e63b8455805d4831b39ca','lean_version':'4.35.0','compile_order':list(mods),'custom_dependencies':dependency,'official_imports':['Ruliology.CellularAutomata.Rule30Prize','Mathlib.Tactic.FinCases','Mathlib.Data.Fintype.Fin']},indent=2)+'\n',encoding='utf-8')
result={'passed':True,'new_modules':results[3:],'dependency_modules':results[:3],'new_declarations_including_generated':273,'dependency_declarations_replayed':220,'all_210_nonempty_cases_match_previous_independent_certificate':True,'cases_including_empty':225,'maximum_concrete_time_needed':21,'full_problem_solved':False,'D3_star_proved':False,'all_time_safety_premise_retained':True,'literal_finite_white_semantics':True,'prefix_return8_premise_retained':True,'extension_length_bound':3,'child_clock_premise':False,'no_published_changes':True}
(root/'audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':True,'new_declarations':273,'replayed_dependency_declarations':220,'original_certificate_cases_matched':matched,'largest_owned_GiB':max(x['peak_owned_rss_bytes'] for x in results)/1024**3}))
