from pathlib import Path
import hashlib,json,shutil
root=Path(__file__).resolve().parent
previous=root.parent/'height2-mixed-mode-20261026T2048'/'delivery-v01'
deps={}
for src in previous.glob('*.lean'):
    shutil.copy2(src,root/src.name)
    deps[src.stem]={'source':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()}
(root/'dependencies.json').write_text(json.dumps(deps,indent=2)+'\n',encoding='utf-8')
p=root/'replay.py';s=p.read_text(encoding='utf-8')
s=s.replace("def replay(module,attempt):", "heads['AnchoredDefectAbstraction']=['genuine_birth_certificate','genuine_birth_antiperiodic','actual_extension_observed','genuine_invariant_saturation','mixed_control_not_separated']\ndef replay(module,attempt):")
s=s.replace("'HeightTwoNearReturn','HeightTwoDescent']:","'HeightTwoNearReturn','HeightTwoDescent','HeightTwoMixedControl']:")
p.write_text(s,encoding='utf-8')
