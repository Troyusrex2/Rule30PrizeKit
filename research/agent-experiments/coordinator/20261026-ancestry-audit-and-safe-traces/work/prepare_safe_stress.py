from pathlib import Path
import ast,hashlib,json
r=Path(__file__).resolve().parent;p=r/'complete_safe_orbits.py';s=p.read_text(encoding='utf-8')
# A single explicit architecture-limited falsification run. The ordinary
# 300s/8GiB/2GiB guard remains unchanged; width33 would exceed it.
s=s.replace('for w in [6,8,12,16,20,24,26]:','for w in [30,32]:')
s=s.replace("r/'complete-safe-orbits.json'","r/'safe-stress-orbits.json'")
(r/'safe_stress_orbits.py').write_text(s,encoding='utf-8')
print(json.dumps({'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'selected_widths':[30,32],
                  'maximum_seen_array_bytes':2**32,'guard_changed':False}))
