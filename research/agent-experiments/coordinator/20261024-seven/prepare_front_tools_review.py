"""Consolidate the checked method and its checked infinite-family use for PR16."""
import hashlib,json,re,subprocess
from core import HERE,BASE

PROJECT=BASE/'front-tools-catalog-20261024'
CA='Ruliology.CellularAutomata.'
CORE=CA+'Rule30ZeroBoundaryStripeFrontLift'
DATA=CA+'Rule30Tail13Completion'
FINAL=CA+'Rule30ZeroBoundaryStripeFourComplete'
NAMES=['Rule30FrontLiftResearch','Rule30FrontPeriodLiftResearch','Rule30FrontLanesResearch','Rule30FrontReturnMapResearch']
MAPPING={n:CORE for n in NAMES}

def body(raw,mapping,drop_self=False):
    raw=re.sub(r'^import .*\n','',raw,flags=re.M)
    for a,b in mapping.items():raw=raw.replace(a,b)
    lines=[]
    for line in raw.splitlines():
        if drop_self and line.startswith('open '):
            words=[w for w in line[5:].split() if w!=CORE]
            if words:lines.append('open '+' '.join(words))
        else:lines.append(line)
    return '\n'.join(lines).strip()+'\n'

def header(imports,doc):
    return 'module\n\n'+''.join('public import '+m+'\n' for m in imports)+'\n/-! '+doc+' -/\n\n@[expose] public section\n\n'

def main():
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip()=='9e72ac6eb43cac734d46942b70d0e4018543ba34'
    root=PROJECT/'lean/Ruliology/CellularAutomata'
    core=header([CA+'Rule30ZeroBoundaryStripeFront',CA+'Rule30ZeroBoundaryLanes'],
        'Width projection, universal return periods, parallel upper-window updates,\n'+
        'and sparse return-map certificate soundness for stripe fronts.')
    for name in NAMES:core+=body((HERE/(name+'.lean')).read_text(encoding='utf-8'),MAPPING,True)+'\n'
    (root/'Rule30ZeroBoundaryStripeFrontLift.lean').write_text(core,encoding='utf-8',newline='\n')
    data=header([CORE],
        'Certificate data for the tail-13 stripe-prefix completion. A punctured\n'+
        'width-34 cycle and a parallel 12-bit return map certify the width-46 cycle.')
    dm={**MAPPING,'Rule30FrontJumpResearch':DATA}
    paths=['Rule30FrontJumpStatesResearch']+[f'Rule30FrontJumpChunk{i:02d}Research' for i in range(9)]
    paths+=['Rule30FrontJumpExecutionResearch','Rule30FrontJumpMapResearch']
    for name in paths:
        data+=body((HERE/'front-jump'/(name+'.lean')).read_text(encoding='utf-8'),dm)+'\n'
    original=(HERE/'external/QuintGeminiFiveTail-f177ae.lean').read_bytes()
    assert hashlib.sha256(original).hexdigest()=='b84849e8f368b030550f586f1c2808e3da74e28e9d93b6b99d808de4f9942689'
    low=original.decode('utf-8')
    first=low[low.index('theorem seg13_0'):low.index('/-- **Control check at `r = 61005`')]
    second=low[low.index('theorem cyc13_period'):low.index('/-- **Punctured front-window soundness')]
    data+='set_option maxRecDepth 200000\nset_option maxHeartbeats 0\n\n'
    data+='namespace '+DATA+'\nopen '+CA+'Rule30ZeroBoundaryStripeFront\n\n'+first+second+'\nend '+DATA+'\n'
    (root/'Rule30Certificates/StripeTail13Completion.lean').write_text(data,encoding='utf-8',newline='\n')
    final=header([CA+'Rule30Certificates.StripeTail13Completion',CA+'Rule30ZeroBoundaryStripeFour'],
        'Complete four-bit stripe-prefix tails. The omitted odd-prefix tail-13\n'+
        'case has an even-time white witness by m+45, from a sparse return-map certificate.')
    fm={**MAPPING,'Rule30FrontJumpResearch':FINAL,'Rule30Submission.cyc13_period':DATA+'.cyc13_period',
        'Rule30Submission.cyc13_sig':DATA+'.cyc13_sig'}
    f=body((HERE/'front-jump/Rule30FrontJumpCycleResearch.lean').read_text(encoding='utf-8'),fm)
    # The data/table declarations now live in their own data namespace.
    f=f.replace('namespace '+FINAL+'\n','namespace '+FINAL+'\nopen '+CORE+' '+DATA+'\n',1)
    f=f[:f.rfind('\nend ')]
    final+=f+'\n\ntheorem cycle13_complete : Cycle 46 45 13 0 2097152 := compressed_cycle\n\n'
    old=(BASE/'stripe13-completion-catalog/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryStripeFourComplete.lean').read_text(encoding='utf-8')
    extra=old[old.index('theorem row4_13_all_odd'):old.rfind('\nend ')]
    final+=extra+'\n\nend '+FINAL+'\n'
    (root/'Rule30ZeroBoundaryStripeFourComplete.lean').write_text(final,encoding='utf-8',newline='\n')
    umbrella=PROJECT/'lean/Ruliology.lean';raw=umbrella.read_text(encoding='utf-8')
    oldmods=['Rule30ZeroBoundaryStripeFrontLift','Rule30ZeroBoundaryStripeFrontPeriod',
             'Rule30ZeroBoundaryStripeFrontParallel','Rule30ZeroBoundaryStripeFrontReturnMap']
    raw='\n'.join(l for l in raw.splitlines() if l not in ['public import '+CA+n for n in oldmods])+'\n'
    anchor='public import '+CA+'Rule30ZeroBoundaryStripeFour\n'
    additions=[CORE,CA+'Rule30Certificates.StripeTail13Completion',FINAL]
    assert raw.count(anchor)==1;raw=raw.replace(anchor,anchor+''.join('public import '+m+'\n' for m in additions))
    umbrella.write_text(raw,encoding='utf-8',newline='\n')
    for name in ['build_all.sh','lean/README.md']:
        path=PROJECT/name;raw=path.read_text(encoding='utf-8')
        anchor='Rule30ZeroBoundaryStripeFamily Rule30ZeroBoundaryStripeFour Rule30EtherTrap'
        assert raw.count(anchor)==1
        replacement=('Rule30ZeroBoundaryStripeFamily Rule30ZeroBoundaryStripeFour \\\n'+
          '    Rule30ZeroBoundaryStripeFrontLift Rule30Certificates.StripeTail13Completion \\\n'+
          '    Rule30ZeroBoundaryStripeFourComplete Rule30EtherTrap')
        raw=raw.replace(anchor,replacement)
        if name.endswith('README.md'):
            lines=[l for l in raw.splitlines() if not any(l.startswith('| `'+m+'`') for m in oldmods)]
            i=next(i for i,l in enumerate(lines) if l.startswith('| `Rule30ZeroBoundaryStripeFour`'))
            rows=[
              '| `Rule30ZeroBoundaryStripeFrontLift` | 2026-10-24 | Front-window projection, universal return periods, parallel simulation and sparse return-map soundness. Contributed by Troy Lowry with OpenAI Codex. | `universal_front_period`, `initial_run_correct`, `return_map_cycle_lift` |',
              '| `Rule30Certificates/StripeTail13Completion` | 2026-10-24 | The punctured width-34 cycle and parallel upper-window return certificate for tail 13. The lower cycle is by G.P.J.W. Quint and Gemini ([R30-20261024-f177ae](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261024-f177ae)); the parallel completion is by Troy Lowry with OpenAI Codex. | `cyc13_period`, `cyc13_sig`, `run_full`, `return_cycle`, `rare_table` |',
              '| `Rule30ZeroBoundaryStripeFourComplete` | 2026-10-24 | Completes the four-bit stripe-tail family, including every odd prefix with tail 13, with a white witness by 45 steps after arrival. Contributed by Troy Lowry with OpenAI Codex, using the catalog stripe-front method and the Quint/Gemini lower cycle. | `row4_13_all_odd`, `stripe_four_tail_complete` |']
            lines[i+1:i+1]=rows;raw='\n'.join(lines)+'\n'
            anchor='| `ZeroBoundaryStripeCycles0`–`3` | `Rule30ZeroBoundaryStripeFamily`, `Rule30ZeroBoundaryStripeFour` | the periodic front-window orbits of the stripe prefixes |\n'
            assert raw.count(anchor)==1
            raw=raw.replace(anchor,anchor+'| `StripeTail13Completion` | `Rule30ZeroBoundaryStripeFourComplete` | a punctured lower cycle and parallel return map complete the omitted tail-13 family |\n')
        path.write_text(raw,encoding='utf-8',newline='\n')
    path=PROJECT/'Rule30PrizeKit.lean';raw=path.read_text(encoding='utf-8')
    assert raw.count('whole catalog, 118 modules')==1
    path.write_text(raw.replace('whole catalog, 118 modules','whole catalog, 121 modules'),encoding='utf-8',newline='\n')
    entries=[]
    heads=[
      ['punctured_cycle_lift','universal_front_period','initial_run_correct','return_map_cycle_lift'],
      ['run_prefix','run_full','return_cycle','rare_table','cyc13_period','cyc13_sig'],
      ['compressed_cycle','compressed_row4_13','cycle13_complete','row4_13_all_odd','stripe_four_tail_complete']]
    for module,namespace,hs in zip(additions,[CORE,DATA,FINAL],heads):
        source='lean/'+module.replace('.','/')+'.lean'
        entries.append({'module':module,'namespace':namespace,'source':source,
          'source_sha256':hashlib.sha256((PROJECT/source).read_bytes()).hexdigest(),
          'headlines':[namespace+'.'+h for h in hs]})
    (HERE/'front-tools-reviewed-manifest.json').write_text(json.dumps({'entries':entries,
      'base_commit':'3eca23c0a9fa6b153313655e6d51835406c2d06e'},indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'prepared_modules':len(entries),'total_source_bytes':sum((PROJECT/e['source']).stat().st_size for e in entries)},flush=True)

if __name__=='__main__':main()
