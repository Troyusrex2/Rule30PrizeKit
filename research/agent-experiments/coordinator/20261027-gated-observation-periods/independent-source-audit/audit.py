from pathlib import Path
import hashlib, json, re, subprocess
from datetime import datetime, timezone

OWN = Path(__file__).resolve().parent
BASE = OWN.parent
FORMAL = BASE / 'gated-observation-reset-formal-20261027T0100'
PAPER = BASE / 'right-gate-reset-audit-20261027T0055'
REPO = Path('D:/MWB/Rule30/clock-demod-catalog-20261027')

def sha(data): return hashlib.sha256(data).hexdigest()
def readjson(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def save(name, data): (OWN/name).write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8', newline='\n')

manifests=[]
for root, expected in [(FORMAL,'bf6efa2942a51a91c3ae1915209422365106b00ebaf197fee9ac34e0de6d0b69'),(PAPER,'2c062c00225a004bb3900ae8dba61ab9c70ce66db759ed48df7e105bcc72f2dd')]:
    mp=root/'MANIFEST.json'
    assert sha(mp.read_bytes())==expected
    entries=[]
    for entry in readjson(mp)['files']:
        p=(root/entry['path']).resolve()
        assert p.is_relative_to(root.resolve())
        data=p.read_bytes()
        assert sha(data)==entry['sha256'],p
        assert len(data)==entry['bytes'],p
        entries.append(entry)
    manifests.append({'directory':str(root),'manifest_sha256':expected,'verified_files':len(entries),'entries':entries})
save('MANIFEST-VERIFICATION.json',manifests)

closure=readjson(FORMAL/'CLOSURE-COMPATIBILITY.json')
mods=closure['modules']
texts={}
checked={}
for name, info in mods.items():
    if info['kind']=='research':
        data=Path(info['local_source']).read_bytes()
        assert sha(data)==info['sha256'],name
        checked[name]={**info,'source_hash_verified':True}
    else:
        bypin={}
        for pin in [closure['compiled_reference_pin'],closure['current_official_pin']]:
            data=subprocess.check_output(['git','-C',str(REPO),'show',f"{pin}:{info['path']}"])
            bypin[pin]=sha(data)
            assert sha(data)==info['sha256'],name
        checked[name]={**info,'git_blob_sha256_by_pin':bypin}
    texts[name]=data.decode('utf-8-sig')

def imports(source):
    # Remove nested Lean block comments, preserving line breaks, before reading import lines.
    out=[]; pos=0; depth=0
    while pos<len(source):
        two=source[pos:pos+2]
        if two=='/-': depth+=1; pos+=2; continue
        if depth and two=='-/': depth-=1; pos+=2; continue
        ch=source[pos]
        out.append(ch if depth==0 or ch=='\n' else ' ')
        pos+=1
    assert depth==0
    return re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+([A-Za-z0-9_.]+)', ''.join(out), re.M)

edges={name:imports(t) for name,t in texts.items()}
seen=set(); todo=['Rule30GatedObservationResetResearch']; unknown=[]
while todo:
    name=todo.pop()
    if name in seen: continue
    seen.add(name)
    for dep in edges[name]:
        if dep not in mods: unknown.append({'from':name,'import':dep})
        else: todo.append(dep)
assert not unknown,unknown
assert seen==set(mods),(seen,set(mods))
save('CLOSURE-VERIFICATION.json',{'actual_module_count':len(seen),'research_count':sum(mods[n]['kind']=='research' for n in seen),'official_count':sum(mods[n]['kind']=='official' for n in seen),'import_edges':edges,'modules':checked,'unknown_imports':unknown})

source=FORMAL/'Rule30GatedObservationResetResearch.lean'
assert sha(source.read_bytes())=='a73205ebbe1316d2a16fd6716cf077245fbe33b206221ea4088df57562880258'
assert sha((PAPER/'PAPER.md').read_bytes())=='219201172d04edb30bd1ed239585e6c79b78eeb1a84e28976990adb4b9b2b03f'
report=readjson(FORMAL/'formal/Rule30GatedObservationResetResearch/report.json')
final=readjson(FORMAL/'FINAL-RESULT.json')
assert report['passed'] and report['source_sha256']==sha(source.read_bytes())
assert report['checker']['replay']=={'constants':24,'ok':True}
assert report['checker']['newAxioms']==[]
assert len(report['checker']['headlines'])==4 and all(h['ok'] and h['typeMatches'] for h in report['checker']['headlines'])
assert final['guard']['exit_code']==0 and final['guard']['guard_stop'] is None
assert final['guard']['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
types=(FORMAL/'formal/Rule30GatedObservationResetResearch/types.log').read_bytes()
(OWN/'REVIEWED-HEADLINE-TYPES.txt').write_bytes(types)
save('RECEIPT-VERIFICATION.json',{'reviewed_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':sha(source.read_bytes()),'paper_sha256':sha((PAPER/'PAPER.md').read_bytes()),'worker_replay_receipt_verified':True,'worker_constants':24,'worker_headlines':4,'new_axioms':[],'checker_sha256':report['checker_sha256'],'compiled_reference_pin':report['pin'],'guard':final['guard'],'independent_checker_execution_by_reviewer':False,'types_sha256':sha(types)})
print(json.dumps({'manifests':[(m['verified_files'],m['manifest_sha256']) for m in manifests],'actual_closure':len(seen),'worker_receipt':'PASS','independent_build':False}))
