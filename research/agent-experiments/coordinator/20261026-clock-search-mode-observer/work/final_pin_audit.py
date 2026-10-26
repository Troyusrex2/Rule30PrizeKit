from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent;p=r/'project'
pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
checker='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
source=json.loads((r/'source-manifest.json').read_bytes());assert source['pin']==pin
for n,h in source['files'].items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
assert hashlib.sha256((p/'Check.lean').read_bytes()).hexdigest()==checker
mods=json.loads((r/'refresh-modules.json').read_bytes())+['Rule30ClockSearchResearch','Rule30ClockModeResearch']
assert len(mods)==41;out=[]
new={'Rule30CubicAlgebraResearch','Rule30ClockSearchResearch','Rule30ClockModeResearch'}
for m in mods:
    b=(r/(m+'.lean')).read_bytes();sha=hashlib.sha256(b).hexdigest()
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',b,re.M)
    f=json.loads((r/'formal'/m/'report.json').read_bytes());c=f['check']
    assert f['passed'] and f['source_sha256']==sha and f['kit_commit']==pin and f['checker_sha256']==checker
    assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms']
    assert all(x['ok'] and x['typeMatches'] for x in c['headlines'])
    g=json.loads((r/'evidence'/('replay-'+m+'.guard.json')).read_bytes())
    assert g['exit_code']==0 and g['guard_stop'] is None and g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
    assert g['elapsed_seconds']<60 and g['peak_owned_rss_bytes']<4*1024**3
    out.append({'module':m,'source_sha256':sha,'declarations':c['replay']['constants'],
                'headlines':len(c['headlines']),'seconds':g['elapsed_seconds'],'peak_rss_bytes':g['peak_owned_rss_bytes'],
                'new_module':m in new})
ref=json.loads((r/'reference-formal/Rule30Equivalents.P2Scales/report.json').read_bytes())
assert ref['passed'] and ref['check']['replay']=={'constants':117,'ok':True} and not ref['check']['newAxioms']
result={'passed':True,'kit_commit':pin,'checker_sha256':checker,'reference_source_files_verified':len(source['files']),
 'modules':out,'module_count':len(out),'total_replayed_declarations':sum(x['declarations'] for x in out),
 'new_module_declarations':sum(x['declarations'] for x in out if x['new_module']),
 'maximum_module_seconds':max(x['seconds'] for x in out),'maximum_module_rss_bytes':max(x['peak_rss_bytes'] for x in out),
 'external_P2Scales_declarations_replayed_separately':117,'full_problem_solved':False}
(r/'final-pin-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='modules'}),flush=True)
