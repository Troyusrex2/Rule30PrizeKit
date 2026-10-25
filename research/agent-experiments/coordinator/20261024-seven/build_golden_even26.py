"""Generate/replay 64 partitioned closed kernel calculations.

Each compiler and checker has its own resource guard. Resume only keeps
matching exact source hashes and full successful replay reports.
"""
import hashlib,json,subprocess,sys
from core import HERE

def main():
    # Three eight-check modules have full successful replay already. A later
    # eight-check replay hit the resource guard; keep the remaining groups
    # smaller, retaining exact checked sources rather than repeating them.
    plan=[(f'Rule30GoldenEven26Chunk{b:02d}Research',range(8*b,8*b+8)) for b in range(3)]
    plan += [(f'Rule30GoldenEven26Part{b:02d}Research',range(4*b,4*b+4)) for b in range(6,16)]
    for module,cases in plan:
        text='import Rule30GoldenEvenSupportResearch\n\n'
        text+='set_option maxRecDepth 200000\nset_option maxHeartbeats 0\n\n'
        text+=f'namespace {module}\nopen Rule30GoldenEvenSupportResearch\n\n'
        heads=[]
        for c in cases:
            heads.append(f'check_{c}')
            text+=f'theorem check_{c} : check 20 {c} 61 = true := by decide +kernel\n\n'
        text+=f'end {module}\n'
        source=HERE/(module+'.lean')
        if source.exists() and source.read_text(encoding='utf-8')!=text:
            raise RuntimeError('Different owned source: '+str(source))
        source.write_text(text,encoding='utf-8',newline='\n')
        out=HERE/'golden-even26-evidence'/module
        report=out/'report.json'
        if report.exists():
            r=json.loads(report.read_text(encoding='utf-8'))
            assert r['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
            assert r['check']['verdict']=='pass' and r['check']['replay']['ok']
            assert not r['check']['newAxioms'] and all(h['ok'] for h in r['check']['headlines'])
            print({'module':module,'stage':'retained_exact_source_pass'},flush=True)
            continue
        print({'module':module,'stage':'fresh_build_and_replay'},flush=True)
        subprocess.run([sys.executable,str(HERE/'verify_research_module.py'),'--module',module,
                        '--headlines',*heads,'--output',str(out)],cwd=HERE,check=True)
    print({'all_64_kernel_checks':'passed'},flush=True)

if __name__=='__main__':main()
