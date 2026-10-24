"""Port checked general front tools into the core catalog, on an isolated branch."""
import hashlib,json,shutil
from core import HERE,BASE

PROJECT=BASE/'front-tools-catalog-20261024'
MAPPING={
 'Rule30FrontLiftResearch':'Rule30ZeroBoundaryStripeFrontLift',
 'Rule30FrontPeriodLiftResearch':'Rule30ZeroBoundaryStripeFrontPeriod',
 'Rule30FrontLanesResearch':'Rule30ZeroBoundaryStripeFrontParallel',
 'Rule30FrontReturnMapResearch':'Rule30ZeroBoundaryStripeFrontReturnMap'}
HEADS={
 'Rule30FrontLiftResearch':['parity_of_bit0','pstep_low','sig_congr','sig_mono','fstep_low','orbit_low','punctured_cycle_lift'],
 'Rule30FrontPeriodLiftResearch':['fstep_top_flip','orbit_phase_lt','orbit_top_flip','fstep_bound','orbit_bound','low_two_choices','double_period','universal_front_period'],
 'Rule30FrontLanesResearch':['scan_length','bscan_length','map_bit_scan','bitMask_bit','project_next','project_run','bscan_getD','represents_next','brun_length','brun_represents','run_represents','word_bound','word_represents','represents_unique','brun_lo_bound','run_correct','allMask_bit','pk_pats','initial_word','initial_run_correct','run_add','run_chain'],
 'Rule30FrontReturnMapResearch':['iter_lt','block_orbit','period_return','exceptional_residues','return_map_cycle_lift']}
SUMMARIES={
 'Rule30FrontLiftResearch':('Projects front orbits to smaller windows and lifts a punctured cycle using explicit checks on its exceptional residues.','orbit_low`, `punctured_cycle_lift'),
 'Rule30FrontPeriodLiftResearch':('Every lower-window return doubles to a return one bit higher; every fitting width-w window has return period 2^w. Return only, not certificate success.','double_period`, `universal_front_period'),
 'Rule30FrontLanesResearch':('Proves bit-parallel high-window simulation above a shared low front window correct for every time, lane and fitting input. Reuses the existing lane-pattern construction.','initial_run_correct`, `run_correct'),
 'Rule30FrontReturnMapResearch':('Builds a higher-window cycle from a finite upper return-map cycle and checks only exceptional lower residues. The return cycle and witness checks remain explicit hypotheses.','return_map_cycle_lift')}

def main():
    entries=[]
    for old,new in MAPPING.items():
        raw=(HERE/(old+'.lean')).read_text(encoding='utf-8')
        for a,b in MAPPING.items():raw=raw.replace(a,'Ruliology.CellularAutomata.'+b)
        raw='module\n\n'+raw.replace('import ','public import ')
        raw=raw.replace('namespace Ruliology.CellularAutomata.'+new,
                        '@[expose] public section\n\nnamespace Ruliology.CellularAutomata.'+new,1)
        raw=raw.replace('namespace Ruliology.CellularAutomata.'+new,
            '/-! Contributed by Troy Lowry and OpenAI Codex. Builds on the catalog\'s\n'+
            'stripe-front and bit-sliced lane methods. Does not prove Q01 or Problem 1. -/\n\n'+
            'namespace Ruliology.CellularAutomata.'+new,1)
        target=PROJECT/'lean/Ruliology/CellularAutomata'/(new+'.lean')
        if target.exists() and target.read_text(encoding='utf-8')!=raw:raise RuntimeError('Different owned catalog module exists')
        target.write_text(raw,encoding='utf-8',newline='\n')
        entries.append({'module':'Ruliology.CellularAutomata.'+new,
                        'source':target.relative_to(PROJECT).as_posix(),
                        'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
                        'headlines':HEADS[old]})
    root=PROJECT/'lean/Ruliology.lean';raw=root.read_text(encoding='utf-8')
    anchor='public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront\n'
    extra=''.join('public import Ruliology.CellularAutomata.'+n+'\n' for n in MAPPING.values())
    if extra not in raw:
        assert raw.count(anchor)==1;raw=raw.replace(anchor,anchor+extra)
    root.write_text(raw,encoding='utf-8',newline='\n')
    readme=PROJECT/'lean/README.md';raw=readme.read_text(encoding='utf-8')
    lines=[line for line in raw.splitlines() if not any(
        line.startswith('| `'+name+'`') for name in MAPPING.values())]
    i=next(i for i,l in enumerate(lines) if l.startswith('| `Rule30ZeroBoundaryStripeFour`'))
    rows=['| `'+new+'` | 2026-10-24 | '+SUMMARIES[old][0]+
          ' Contributed by Troy Lowry with OpenAI Codex. | `'+SUMMARIES[old][1]+'` |'
          for old,new in MAPPING.items()]
    lines[i+1:i+1]=rows;raw='\n'.join(lines)+'\n'
    readme.write_text(raw,encoding='utf-8',newline='\n')
    (HERE/'front-tools-catalog-manifest.json').write_text(json.dumps({'entries':entries,
       'base_commit':'3eca23c0a9fa6b153313655e6d51835406c2d06e'},indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'modules':len(entries),'project':str(PROJECT)},flush=True)

if __name__=='__main__':main()
