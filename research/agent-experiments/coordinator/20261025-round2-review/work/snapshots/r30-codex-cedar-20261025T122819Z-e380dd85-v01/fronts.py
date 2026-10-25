"""Test the Rule-30-specific frontier and nonlinear Rule-210 control."""
import itertools,json,random,time
from pathlib import Path
from experiment import step,phi,decode,rule,normalization

ROOT=Path(__file__).resolve().parent

def derivative_active(a,b,x,gauge,number):
    d=a^b
    # f = left XOR g(center,right), g(c,r)=f(0,c,r).
    right=int(x+1 in (a if gauge==0 else b))
    center=int(x in (b if gauge==0 else a))
    wc=rule(0,0,right,number)^rule(0,1,right,number)
    wr=rule(0,center,0,number)^rule(0,center,1,number)
    return [p for p,w in zip((x-1,x,x+1),(1,wc,wr)) if w and p in d]

def structural_controls():
    controls=[]
    for number in (30,90,150,210):
        failed=[]
        for v in itertools.product((0,1),repeat=6):
            a={p for p,b in zip((-1,0,1),v[:3]) if b}
            b={p for p,b in zip((-1,0,1),v[3:]) if b}
            out=rule(*v[:3],number)^rule(*v[3:],number)
            for gauge in (0,1):
                assert len(derivative_active(a,b,0,gauge,number))%2==out
            if out:
                wanted=min(a^b)
                if not any(wanted in derivative_active(a,b,0,g,number) for g in (0,1)):
                    failed.append({'a':list(v[:3]),'b':list(v[3:]),'wanted_parent':wanted})
        controls.append({'rule':number,'local_cases':64,'normalization_failures':len(failed),
                         'first_failure':failed[0] if failed else None})
    # Nonlinear coupled-seed control. T=P=1 gives identical center outputs forever.
    a=step({0},210);b=step(a,210);roots={x:x for x in a^b}
    left=min(roots); records=[]
    r90={0}; r210={0}
    for t in range(257):
        assert r90==r210
        assert all((x-t)%2==0 for x in r210)
        assert r210=={-x for x in r210}
        assert (0 in r210)==(t==0)
        r90=step(r90,90);r210=step(r210,210)
        assert 0 not in a^b
        assert left in roots.values()
        front=max(x for x in roots if roots[x]==left)
        assert front<0
        if t<16:
            records.append({'time':t,'a':sorted(a),'b':sorted(b),
                            'left_root_front':front,'center_disagreement':0})
        an=step(a,210);bn=step(b,210)
        roots={x:roots[min(p for p in (x-1,x,x+1) if p in roots)] for x in an^bn}
        sequence=[roots[x] for x in sorted(roots)]
        assert sequence==sorted(sequence)
        a,b=an,bn
    return {'local_rule_comparisons':controls,'rule210_seed_rows_checked':257,
            'rule210_canonical_pair':{'T':1,'P':1,'initial_left_root':left,'first_16_rows':records}}

def scan(T,P,rows,horizon,keep=False):
    a=rows[T]<<P;b=rows[T+P];frame=T+P
    d=a^b;root=1<<(d.bit_length()-1)
    front=frame-(root&-root).bit_length()+1
    high=front;at_high=0;max_stall=0;first_hit=None;first_retreat=None
    records=[];largest_drop=0
    for t in range(horizon+1):
        now=frame+t-(root&-root).bit_length()+1
        if now<front:
            largest_drop=max(largest_drop,front-now)
            if first_retreat is None:
                first_retreat={'time_before':t-1,'time_after':t,'front_before':front,'front_after':now}
        if now>high:
            max_stall=max(max_stall,t-at_high)
            high=now;at_high=t
        if first_hit is None and (root>>(frame+t))&1: first_hit=t
        if keep:
            records.append({'t':t,'a_hex':hex(a),'b_hex':hex(b),'root_hex':hex(root),
                            'frame':frame+t,'front':now,'center_has_left_root':bool((root>>(frame+t))&1)})
        if t==horizon: break
        an=phi(a);bn=phi(b)
        nextroot=(an^bn)&(root|(root<<1)|(root<<2))
        assert nextroot
        if keep:
            pa=decode(a,frame+t);pb=decode(b,frame+t);pr=decode(root,frame+t)
            independent=set()
            for x in step(pa)^step(pb):
                parent=normalization(pa,pb,x)[0]
                if parent in pr: independent.add(x)
            assert decode(nextroot,frame+t+1)==independent
        a,b,root=an,bn,nextroot;front=now
    return {'T':T,'P':P,'horizon':horizon,'first_left_root_center_hit':first_hit,
            'first_retreat':first_retreat,'largest_drop':largest_drop,
            'max_completed_high_water_stall':max_stall,'final_front':now,'records':records}

def main():
    start=time.monotonic()
    out={'structural_controls':structural_controls()}
    rows=[1]
    for _ in range(16384): rows.append(phi(rows[-1]))
    cases=[]; first_retreat=None;missing=[]
    for total in range(1,129):
        for P in range(1,total+1):
            T=total-P
            if T>63 or P>64: continue
            r=scan(T,P,rows,4*total+128)
            cases.append({k:v for k,v in r.items() if k!='records'})
            if first_retreat is None and r['first_retreat']:
                first_retreat=(T,P,r['first_retreat']['time_after'])
            if r['first_left_root_center_hit'] is None: missing.append([T,P])
    rng=random.Random(30720261025);holdout=[]
    for _ in range(32):
        T=rng.randrange(64,8193);P=rng.randrange(65,8193)
        r=scan(T,P,rows,4*(T+P)+128)
        holdout.append({k:v for k,v in r.items() if k!='records'})
    witness=scan(first_retreat[0],first_retreat[1],rows,first_retreat[2]+2,True) if first_retreat else None
    out.update({'rectangle':{'T':[0,63],'P':[1,64],'horizon':'4*(T+P)+128'},
                'ordered_by':'T+P then P','rectangle_cases':cases,'no_hit_in_rectangle':missing,
                'holdout_seed':30720261025,'holdout_sampling':'32 independent uniform integers T in [64,8192], P in [65,8192]',
                'holdout_cases':holdout,'first_retreat_witness':witness,
                'elapsed_seconds':time.monotonic()-start})
    (ROOT/'evidence'/'fronts.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'rectangle_cases':len(cases),'no_hit':missing,'first_retreat':first_retreat,
                      'witness':witness,'holdout_no_hits':[(r['T'],r['P']) for r in holdout if r['first_left_root_center_hit'] is None],
                      'worst_drop':max(r['largest_drop'] for r in cases+holdout),
                      'max_stall':max(r['max_completed_high_water_stall'] for r in cases+holdout),
                      'seconds':out['elapsed_seconds']}))

if __name__=='__main__':main()
