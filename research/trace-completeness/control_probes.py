"""Independent scalar and exhaustive small-domain controls for the probes."""
import json
from pathlib import Path
import edge_completeness_width_probe as edge

HERE=Path(__file__).resolve().parent

def scalar_trace(row,c,horizon):
    cells={c-i:(row>>i)&1 for i in range(row.bit_length())}
    result=0
    for t in range(horizon):
        result |= cells.get(0,0)<<t
        if not cells:continue
        out={}
        for x in range(min(cells)-1,max(cells)+2):
            neighborhood=(cells.get(x-1,0)<<2)|(cells.get(x,0)<<1)|cells.get(x+1,0)
            value=(30>>neighborhood)&1
            if value:out[x]=value
        cells=out
    return result

def main():
    data=json.loads((HERE/'edge-completeness-width-probe.json').read_text())
    tested=pairs=0
    for record in data['results']:
        n,c,h=record['initial_bit_bound'],record['center_index'],record['horizon']
        if n>8:continue
        traces=[edge.probe.trace(a,c,h) for a in range(1<<n)]
        direct=-1
        for a in range(1,1<<n):
            for b in range(1,a):
                if a.bit_length()==b.bit_length():continue
                pairs+=1
                delta=traces[a]^traces[b]
                assert delta,(n,c,a,b)
                direct=max(direct,(delta&-delta).bit_length()-1)
        assert direct==record['longest_different_edge_common_prefix'],record
        tested+=1
    scalar=0
    for a,b,c in [(17,25,4),(33,45,5),(49,48,3),(38212,31279,4)]:
        for row in (a,b):
            assert scalar_trace(row,c,80)==edge.probe.trace(row,c,80),(row,c)
            scalar+=80
    delta=scalar_trace(33,5,59)^scalar_trace(45,5,59)
    assert (delta&-delta).bit_length()-1==58
    report={'verdict':'pass','finite_controls_only':True,'small_domain_cases':tested,
            'naive_different_edge_pairs':pairs,'independent_scalar_trace_observations':scalar,
            'six_bit_pair_first_difference':58,'full_problem_solved':False}
    (HERE/'probe-controls.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))

if __name__=='__main__':main()
