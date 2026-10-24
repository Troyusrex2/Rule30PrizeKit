"""Reproduce only the finite certificate data; never change the proof bodies."""
import argparse
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]


def pool(clock):
    mask=(1<<clock)-1;seen={0};queue=[0]
    def integrate(rhs):
        a=bit=0
        for t in range(clock):a|=bit<<t;bit^=(rhs>>t)&1
        return a,bit
    for key in queue:
        b,c=key&mask,key>>clock;a,odd=integrate(b|c)
        if odd:continue
        for value in (a,a^mask):
            target=value|(b<<clock)
            if target not in seen:seen.add(target);queue.append(target)
    result=[]
    for key in queue:
        b,c=key&mask,key>>clock;a,_=integrate(b|c);result.append((b,c,a,a^mask))
    return result


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write',action='store_true')
    args=ap.parse_args();entries=pool(16);assert len(entries)==68
    body=',\n'.join('  Node.mk '+' '.join(map(str,e)) for e in entries)
    path=ROOT/'lean/Ruliology/CellularAutomata/Rule30FiniteClockSixteenResearch.lean'
    source=path.read_text(encoding='utf-8');begin='def pool16 : List Node := [\n';end=']\n\nset_option'
    left,middle=source.split(begin,1);old,right=middle.split(end,1)
    generated=left+begin+body+end+right
    if args.write:path.write_text(generated,encoding='utf-8',newline='\n')
    else:assert old==body,'Certificate data differs; inspect before regenerating'
    report={'generator_is_not_proof_verification':True,'full_problem_claim':False,'clock':16,
            'nodes':len(entries),'head_clock_residues_checked':list(range(16)),'generated_data_matches':True,
            'proof_bodies_changed':False,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
    (HERE/'finite-clock16-discovery.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__':main()
