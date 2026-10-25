from pathlib import Path
import json
root=Path(__file__).resolve().parent
certs=[json.loads(line) for line in (root/'common-certificates.jsonl').read_text(encoding='utf-8').splitlines()]
records=[]
for c in certs:
    rows=c['rows'];U,V=c['U'],c['V']
    local=[r for r in rows if r[0]!='O']
    records.append({'U':U,'V':V,'rows':len(rows),'observations':c['observation_times'],
      'max_time':c['maximum_certificate_time'],
      'min_position':min(r[2] for r in rows),'max_position':max(r[2] for r in rows),
      'selected_constraints_right_of_center':sum(r[2]>0 for r in local),
      'left_comoving_depths_in_A':sorted({r[2]+r[1]+U for r in local}),
      'last_time_minus_U':c['maximum_certificate_time']-U})
out={'finite_only':True,'records':records,
     'any_right_of_center':sum(r['selected_constraints_right_of_center']>0 for r in records),
     'max_last_time_minus_U':max(r['last_time_minus_U'] for r in records),
     'largest_certificates':sorted(records,key=lambda r:r['rows'],reverse=True)[:5],
     'example':next(c for c in certs if (c['U'],c['V'])==(16,15))}
(root/'certificate-analysis.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ('records','example')},indent=2))
print(json.dumps(out['example']))
