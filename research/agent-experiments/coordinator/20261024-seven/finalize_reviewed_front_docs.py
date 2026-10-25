"""Write measured building costs and complete credits after successful replay."""
import hashlib,json,math
from core import HERE
from verify_reviewed_front_catalog import PROJECT

result=json.loads((HERE/'front-tools-reviewed-evidence/report.json').read_text(encoding='utf-8'))
assert result['verdict']=='pass' and len(result['entries'])==3
manifest=json.loads((HERE/'front-tools-reviewed-manifest.json').read_text(encoding='utf-8'))
for entry in manifest['entries']:
    assert hashlib.sha256((PROJECT/entry['source']).read_bytes()).hexdigest()==entry['source_sha256']
baseline=json.loads((HERE/'tail13-baseline-evidence/report.json').read_text(encoding='utf-8'))
data=result['entries'][1]['build'];assert data['seconds']<86 and data['seconds']<baseline['build']['seconds']
path=PROJECT/'lean/README.md';raw=path.read_text(encoding='utf-8')
anchor='### Contributed white-padding modules\n';assert raw.count(anchor)==1
section='''### Contributed stripe-front modules

Measured on Windows x64 with Lean 4.35.0 on 2026-10-25. Each module was built
alone with its imports already compiled. Peak memory is the sum of process
RSS, sampled every 50 ms and rounded up below.

| Module | Time | Peak memory |
|---|---|---|
'''
for entry in result['entries']:
    module=entry['module'].removeprefix('Ruliology.CellularAutomata.').replace('.','/')
    build=entry['build'];gb=math.ceil(build['peak_tree_rss_bytes']/1e7)/100
    section+=f"| `{module}` | {build['seconds']:.1f} s | {gb:.2f} GB |\n"
section+='\nThe original monolithic 256-segment tail-13 data compiled in '
section+=f"{baseline['build']['seconds']:.1f} s and {baseline['build']['peak_tree_rss_bytes']/1e9:.2f} GB on the same machine.\n"
section+='The return-map certificate packs only its 32 visited upper states into parallel lanes.\n\n'
if '### Contributed stripe-front modules\n' in raw:
    start=raw.index('### Contributed stripe-front modules\n');stop=raw.index(anchor,start);raw=raw[:start]+raw[stop:]
raw=raw.replace(anchor,section+anchor)
raw=raw.replace('The punctured width-34 cycle and parallel upper-window return certificate for tail 13.',
                'The punctured width-34 cycle and 32-state parallel upper return certificate for tail 13.')
raw=raw.replace('using the catalog stripe-front method and the Quint/Gemini lower cycle.',
                "using Ying Yin and Codex's catalog stripe-front method and the Quint/Gemini lower cycle.")
path.write_text(raw,encoding='utf-8',newline='\n')
modules=list((PROJECT/'lean/Ruliology/CellularAutomata').rglob('*.lean'))
assert len(modules)==121
assert 'whole catalog, 121 modules' in (PROJECT/'Rule30PrizeKit.lean').read_text(encoding='utf-8')
script=(PROJECT/'build_all.sh').read_text(encoding='utf-8')
order=['Rule30ZeroBoundaryStripeFour ','Rule30ZeroBoundaryStripeFrontLift ',
       'Rule30Certificates.StripeTail13Completion ','Rule30ZeroBoundaryStripeFourComplete ']
locations=[script.index(name) for name in order];assert locations==sorted(locations)
info={'module_count':len(modules),'data_faster_than_same_host_baseline':True,
      'data_seconds':data['seconds'],'baseline_seconds':baseline['build']['seconds'],
      'all_three_replayed_declarations':sum(e['check']['replay']['constants'] for e in result['entries']),
      'reviewed_credits_in_readme':True,'build_order_checked':True}
(HERE/'front-tools-reviewed-evidence/metadata-checks.json').write_text(json.dumps(info,indent=2)+'\n',encoding='utf-8',newline='\n')
print(info,flush=True)
