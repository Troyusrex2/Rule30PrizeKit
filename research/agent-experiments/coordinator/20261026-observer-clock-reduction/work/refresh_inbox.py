from pathlib import Path
import hashlib,json,datetime
r3=Path(r'D:\MWB\Rule30\wolfram-local\agent-seven-20261024\round3-evaluation-20261026T0103')
root=Path(__file__).resolve().parent
inbox=Path(r'D:\MWB\Rule30\agent-inbox')
known={r['response']:r for r in json.loads((r3/'intake-seven.json').read_bytes())['responses']}
new=[];changed=[]
for p in inbox.iterdir():
    if not p.is_dir() or not (p/'READY').exists():continue
    if p.name in known:
        diff=[n for n,h in known[p.name]['files'].items() if not (p/n).exists() or hashlib.sha256((p/n).read_bytes()).hexdigest()!=h]
        if diff:changed.append({'response':p.name,'changed_files':diff})
    elif p.name.startswith('r30-') and p.stat().st_mtime>datetime.datetime(2026,10,26,0,50,tzinfo=datetime.timezone.utc).timestamp():new.append(p.name)
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'new_ready_since_round3':new,'changed_round3':changed}
(root/'inbox-refresh.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
