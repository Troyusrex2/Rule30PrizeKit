"""Generate small ordinary-kernel equality proofs for a large trace mask.

No native_decide or solver proof oracle. Every leaf equality is by decide;
internal nodes combine already proved equalities with one exact OR operation.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('obs',HERE/'trace-observability.py')
obs=importlib.util.module_from_spec(spec)
spec.loader.exec_module(obs)
LIB=PROJECT/'lean/Ruliology/CellularAutomata'
CERT=LIB/'Rule30Certificates'
PREFIX='Ruliology.CellularAutomata.'


def leaf_mask(h,c,b,start):
    mask=0
    for row in range(start,start+(1<<b)):
        mask |= 1<<obs.center_trace(row,c,h)
    return mask


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--leaf-bits',type=int,default=11)
    parser.add_argument('--per-module',type=int,default=8)
    args=parser.parse_args()
    records=[]
    h=15
    for m in [2,3]:
        total=h-1+m
        chunk_count=1<<(total-args.leaf_bits)
        names=[]
        masks=[]
        for first in range(0,chunk_count,args.per_module):
            index=first//args.per_module
            name=f'TraceSepH15M{m}Chunk{index}'
            names.append('Rule30Certificates.'+name)
            lines=['module','','public import '+PREFIX+'Rule30TraceSeparationResearch','',
                   '/-! Generated finite certificate leaves. Each equality is replayed by the kernel. -/','',
                   '@[expose] public section','',
                   'namespace '+PREFIX+'Rule30TraceSeparationData',
                   'open Rule30TraceSeparationResearch','']
            for i in range(first,min(first+args.per_module,chunk_count)):
                start=(1<<total)+(i<<args.leaf_bits)
                mask=leaf_mask(h,h-1,args.leaf_bits,start)
                masks.append(mask)
                lines += ['set_option maxHeartbeats 0 in',
                          f'theorem m{m}_leaf_{i} : allSignatures {h} {h-1} {args.leaf_bits} {start} = {hex(mask)} := by decide','']
            lines+=['end '+PREFIX+'Rule30TraceSeparationData','']
            path=CERT/(name+'.lean')
            path.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
            records.append({'module':PREFIX+'Rule30Certificates.'+name,
                            'relative_path':path.relative_to(PROJECT).as_posix(),
                            'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
        lines=['module','']+['public import '+PREFIX+n for n in names]+['',
               '@[expose] public section','',
               'namespace '+PREFIX+'Rule30TraceSeparationData',
               'open Rule30TraceSeparationResearch','',
               '/-- Combine symbolic children before specializing to large ground cones. -/',
               f'theorem m{m}_join {{H C B a l r s : Nat}}',
               '    (hl : allSignatures H C B a = l)',
               '    (hr : allSignatures H C B (a+2^B) = r)',
               '    (hor : Nat.lor l r = s) : allSignatures H C (B+1) a = s := by',
               '  rw [allSignatures,hl,hr]', '  exact hor','']
        previous=[(f'm{m}_leaf_{i}',mask) for i,mask in enumerate(masks)]
        bits=args.leaf_bits
        while len(previous)>1:
            current=[]
            for j in range(0,len(previous),2):
                a,am=previous[j];b,bm=previous[j+1]
                start=(1<<total)+((j//2)<<(bits+1))
                mask=am|bm
                name=f'm{m}_node_{bits+1}_{j//2}'
                lines += [f'theorem {name} : allSignatures {h} {h-1} {bits+1} {start} = {hex(mask)} := by',
                          f'  exact m{m}_join {a} {b} (by decide)','']
                current.append((name,mask))
            bits+=1
            previous=current
        root,root_mask=previous[0]
        lines += [f'theorem m{m}_full_mask : edgeSignatures {h} {m} = {hex(root_mask)} := by',
                  f'  exact {root}','',
                  'end '+PREFIX+'Rule30TraceSeparationData','']
        path=CERT/f'TraceSepH15M{m}.lean'
        path.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
        records.append({'module':PREFIX+f'Rule30Certificates.TraceSepH15M{m}',
                        'relative_path':path.relative_to(PROJECT).as_posix(),
                        'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    report={'generator':'generate-separation-chunks.py','horizon':15,'left_depths':[2,3],
            'leaf_bits':args.leaf_bits,'per_module':args.per_module,'modules':records}
    (HERE/'separation-chunk-manifest.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'generated_modules':len(records),'leaf_bits':args.leaf_bits}))


if __name__=='__main__':
    main()
