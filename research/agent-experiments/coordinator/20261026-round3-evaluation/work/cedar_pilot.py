"""Exact complete-interface elimination, followed by a falsifiable lift pilot."""
from pathlib import Path
import hashlib,itertools,json,time
import psutil
ROOT=Path(__file__).resolve().parent
started=time.monotonic();peak=0
def guard():
    global peak
    peak=max(peak,psutil.Process().memory_info().rss)
    assert time.monotonic()-started<60
    assert peak<256*2**20
def F(a):return a^((a<<1)|(a<<2))
rows=[1]
for _ in range(140):rows.append(F(rows[-1]))
def cell(t,p):
    j=t-p
    return (rows[t]>>j)&1 if j>=0 else 0
def cone(U,V,T,x=0):
    coords=[(t,p) for t in range(T+1) for p in range(x-(T-t),x+T-t+1)]
    ids={coord:i for i,coord in enumerate(coords)}
    equations=[];labels=[]
    def add(terms,label):
        r=0
        for coord in terms:r^=1<<ids[coord]
        if r:equations.append(r);labels.append(label)
    for t in range(T):
        radius=T-t
        for p in range(x-radius+1,x+radius):
            terms=[(t+1,p),(t,p-1)]
            if not cell(V+t,p+1):terms.append((t,p))
            if not cell(U+t,p):terms.append((t,p+1))
            add(terms,['D',t,p])
        for p in range(x-radius,x+radius):
            terms=[]
            if cell(U+t,p+1)^cell(V+t,p+1):terms.append((t,p))
            if cell(U+t,p)^cell(V+t,p):terms.append((t,p+1))
            add(terms,['W',t,p])
    actual=sum((cell(U+t,p)^cell(V+t,p))<<i for i,(t,p) in enumerate(coords))
    assert all((r&actual).bit_count()%2==0 for r in equations)
    return coords,ids,equations,labels,actual
def project(equations,interior):
    pivots={}
    for j,row in enumerate(equations):
        proof=1<<j
        while row:
            active=row&interior
            pivot=(active or row).bit_length()-1
            if pivot not in pivots:
                pivots[pivot]=(row,proof);break
            old,origin=pivots[pivot];row^=old;proof^=origin
    result=[]
    for row,proof in pivots.values():
        if row&interior:continue
        reconstructed=0
        for j,original in enumerate(equations):
            if proof>>j&1:reconstructed^=original
        assert reconstructed==row
        result.append((row,proof))
    return result
def canonical(equations):
    pivots={}
    for row in equations:
        while row:
            p=row.bit_length()-1
            if p not in pivots:pivots[p]=row;break
            row^=pivots[p]
    for p in sorted(pivots):
        for q in pivots:
            if q>p and pivots[q]>>p&1:pivots[q]^=pivots[p]
    return sorted(pivots.values())

prior=ROOT/'prior-deadline-certificates.jsonl'
wanted={(4,3),(8,7),(16,15),(32,31),(33,31),(40,1)}
reused=[]
for line in prior.read_text().splitlines():
    certificate=json.loads(line);U,V=certificate['U'],certificate['V']
    if (U,V) not in wanted:continue
    total=set();blocks={};observations=set()
    for kind,t,p in certificate['rows']:
        if kind=='O':
            terms={(t,p),('O',t)};observations.symmetric_difference_update({('O',t)})
        elif kind=='D':
            terms={(t+1,p),(t,p-1)}
            if not cell(V+t,p+1):terms.symmetric_difference_update({(t,p)})
            if not cell(U+t,p):terms.symmetric_difference_update({(t,p+1)})
        elif kind=='W':
            terms=set()
            if cell(U+t,p+1)^cell(V+t,p+1):terms.symmetric_difference_update({(t,p)})
            if cell(U+t,p)^cell(V+t,p):terms.symmetric_difference_update({(t,p+1)})
        else:raise AssertionError(kind)
        # Only the proved forward cone from initial support [-U,U] is zero.
        terms={q for q in terms if q[0]=='O' or -U-q[0]<=q[1]<=U+q[0]}
        total.symmetric_difference_update(terms)
        blocks.setdefault(t//2,set()).symmetric_difference_update(terms)
    expected={(0,-U)}|observations
    assert total==expected
    assert all(q[0]=='O' or q[0]%2==0 for residual in blocks.values() for q in residual)
    glued=set()
    for residual in blocks.values():glued.symmetric_difference_update(residual)
    assert glued==expected
    reused.append({'U':U,'V':V,'blocks':len(blocks),'readout_terms':len(observations),
                   'exact_source_plus_readout':True,'all_seam_coordinates_retained':True})
assert len(reused)==len(wanted)

cases=[];assignments=0
for U,V in [(1,0),(2,1),(5,3),(9,7),(17,15),(33,31),(65,63)]:
    guard()
    coords,ids,eq,labels,actual=cone(U,V,2)
    boundary=[i for i,(t,p) in enumerate(coords) if t in (0,2)]
    internal=[i for i,(t,p) in enumerate(coords) if t==1]
    interior=sum(1<<i for i in internal)
    projected=project(eq,interior)
    for values in range(1<<len(boundary)):
        base=sum(((values>>j)&1)<<i for j,i in enumerate(boundary))
        feasible=any(all((r&(base|sum(((z>>j)&1)<<i for j,i in enumerate(internal)))).bit_count()%2==0 for r in eq)
                     for z in range(1<<len(internal)))
        predicted=all((r&base).bit_count()%2==0 for r,_ in projected)
        assert feasible==predicted
        assignments+=1
    # Four-step cone: eliminate interiors in two blocks, retain all seam
    # variables, glue, then eliminate the complete seam.
    c4,i4,e4,l4,a4=cone(U,V,4)
    lower=[r for r,l in zip(e4,l4) if l[1]<2]
    upper=[r for r,l in zip(e4,l4) if l[1]>=2]
    at1=sum(1<<i for i,(t,p) in enumerate(c4) if t==1)
    at3=sum(1<<i for i,(t,p) in enumerate(c4) if t==3)
    seam=sum(1<<i for i,(t,p) in enumerate(c4) if t==2)
    joined=[r for r,_ in project(lower,at1)]+[r for r,_ in project(upper,at3)]
    via_blocks=canonical([r for r,_ in project(joined,seam)])
    direct=canonical([r for r,_ in project(e4,at1|seam|at3)])
    assert via_blocks==direct
    cases.append({'U':U,'V':V,'full_boundary_projection':True,'block_gluing_exact':True,
                  'boundary_relations':len(projected),'all_unwanted_coordinates_canceled':True})

# First proposed scale identity: double coordinates in one coarse D row,
# using the coarse coefficients, and try to derive it in the fine block.
coarseU,coarseV=1,0
coords,ids,eq,labels,actual=cone(2*coarseU,2*coarseV,2)
lift=(1<<ids[(2,0)])^(1<<ids[(0,-2)])
if not cell(coarseV,1):lift^=1<<ids[(0,0)]
if not cell(coarseU,0):lift^=1<<ids[(0,2)]
assert (lift&actual).bit_count()%2==1
counter={'coarse_ages':[1,0],'fine_ages':[2,0],
         'lifted_row_coordinates':[list(coords[i]) for i in range(len(coords)) if lift>>i&1],
         'actual_fine_difference_values':[{'t':t,'p':p,'h':actual>>i&1} for i,(t,p) in enumerate(coords)],
         'every_fine_D_and_W_zero':True,'lifted_coarse_row_value':1,
         'canonical_counter_to_naive_row_lift':True}
guard()
report={'passed':True,'finite_pilot':True,'Lean_verified':False,
        'complete_interface_cases':cases,'boundary_assignments_checked':assignments,
        'prior_certificates_replayed':reused,
        'prior_certificate_file_sha256':hashlib.sha256(prior.read_bytes()).hexdigest(),
        'naive_coordinate_doubling_refuted':counter,
        'nontrivial_Rule30_specific_induction_lift_found':False,
        'missing_premise':'A scale identity that changes center reach while retaining complete boundary relations and canonical background data.',
        'seconds':round(time.monotonic()-started,3),'peak_rss_bytes':peak,
        'limits':{'seconds':60,'rss_bytes':256*2**20},'full_problem_solved':False}
(ROOT/'cedar-pilot.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['complete_interface_cases','naive_coordinate_doubling_refuted']}),flush=True)
