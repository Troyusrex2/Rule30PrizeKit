from pathlib import Path
import hashlib,json,shutil
root=Path(__file__).resolve().parent
previous=root.parent/'height2-descent-20261026T2016'/'delivery-v01'
deps={}
for src in previous.glob('*.lean'):
    shutil.copy2(src,root/src.name)
    deps[src.stem]={'source':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()}
(root/'dependencies.json').write_text(json.dumps(deps,indent=2)+'\n',encoding='utf-8')
p=root/'replay.py';s=p.read_text(encoding='utf-8')
s=s.replace("def replay(module,attempt):", "heads['HeightTwoMixedControl']=['all_time_local_constraints','newest_span_two','newest_not_eight','neither_parent_safe_or_coSafe','neither_parent_height_two']\ndef replay(module,attempt):")
p.write_text(s,encoding='utf-8')
