"""Port the already replayed four-tail completion to core catalog module paths."""
from pathlib import Path
import hashlib,json
from core import HERE,BASE

def main():
    project=BASE/'stripe13-completion-catalog';src=HERE/'tail13-completion'
    cert=project/'lean/Ruliology/CellularAutomata/Rule30Certificates';cert.mkdir(exist_ok=True)
    mapping={f'Rule30Tail13Chunk{i:02d}':f'Ruliology.CellularAutomata.Rule30Certificates.StripeTail13Completion{i:02d}' for i in range(32)}
    mapping['Rule30Tail13Complete']='Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFourComplete'
    entries=[]
    for old,new in mapping.items():
        raw=(src/(old+'.lean')).read_text(encoding='utf-8')
        for a,b in mapping.items():raw=raw.replace('public import '+a+'\n','public import '+b+'\n')
        if old=='Rule30Tail13Complete':
            raw=raw.replace('This is not Q01 or a solution of a prize problem. -/',
                'Troy Lowry and Codex completed this case after independently replaying\n'+
                'G.P.J.W. Quint and Gemini\'s punctured width-34 cycle (submission\n'+
                'R30-20261024-f177ae). The front-window method and the other four-tail\n'+
                'classes are from the existing catalog, including Ying Yin and Codex.\n'+
                'No new method, Q01 proof, or prize solution is claimed. -/')
        target=project/'lean'/Path(*new.split('.')).with_suffix('.lean')
        if target.exists() and target.read_text(encoding='utf-8')!=raw:raise RuntimeError('Different catalog file exists: '+str(target))
        target.write_text(raw,encoding='utf-8',newline='\n')
        entries.append({'module':new,'source':str(target.relative_to(project)).replace('\\','/'),
                        'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
                        'headlines':['complete_path','cycle13_complete','row4_13_all_odd','stripe_four_tail_complete'] if old=='Rule30Tail13Complete' else ['path_chunk_'+old[-2:]]})
    root=project/'lean/Ruliology.lean';text=root.read_text(encoding='utf-8')
    newline='public import '+mapping['Rule30Tail13Complete']
    anchor='public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFour'
    if newline not in text:text=text.replace(anchor+'\n',anchor+'\n'+newline+'\n')
    root.write_text(text,encoding='utf-8',newline='\n')
    readme=project/'lean/README.md';text=readme.read_text(encoding='utf-8')
    row='| `Rule30ZeroBoundaryStripeFourComplete` | 2026-10-24 | Completes the omitted tail `13` with odd stripe-prefix length in `Rule30ZeroBoundaryStripeFour`, using a width-46 front cycle of period `2^21`, split into 32 checked data modules. Every prefix length `m` and every four-cell tail now has an even white witness by `d - 1 + 45`, where the first deviation has depth `d ≤ m + 6`. The front method is unchanged; Q01 and arbitrary finite tails remain open. Contributed by Troy Lowry with Codex, following the independently replayed punctured cycle of G.P.J.W. Quint and Gemini (`R30-20261024-f177ae`). | `stripe_four_tail_complete`, `row4_13_all_odd`, `cycle13_complete` |'
    if '| `Rule30ZeroBoundaryStripeFourComplete`' not in text:
        lines=text.splitlines();index=next(i for i,l in enumerate(lines) if l.startswith('| `Rule30ZeroBoundaryStripeFour`'))
        lines.insert(index+1,row);text='\n'.join(lines)+'\n'
    if '| `StripeTail13Completion00`' not in text:
        lines=text.splitlines();index=next(i for i,l in enumerate(lines) if l.startswith('| `ZeroBoundaryStripeCycles0`'))
        lines.insert(index+1,'| `StripeTail13Completion00`–`31` | `Rule30ZeroBoundaryStripeFourComplete` | the complete width-46, period-`2^21` front cycle for the omitted `(13, 0)` class |')
        text='\n'.join(lines)+'\n'
    readme.write_text(text,encoding='utf-8',newline='\n')
    out={'kit_commit':'3eca23c0a9fa6b153313655e6d51835406c2d06e','entries':entries,'full_problem_solved':False}
    (HERE/'catalog-tail13-manifest.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    print({'catalog_modules':len(entries),'project':str(project)},flush=True)

if __name__=='__main__':main()
