"""Freeze supplied diagnostic sources and adapt our private replay helper."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
LIVE=Path('D:/MWB/Rule30/wolfram-local/agent-seven-20261024/global-clock-20261026T1650')
MODULE='Rule30CyclicSubsetObstructionResearch'
SHA='4c7afb6a97daeb6c0305a07cc0a6b54f3a74f2dc65e387d9b5026333c760b45e'
files=[MODULE+'.lean','formal/'+MODULE+'/report.json','evidence/replay-'+MODULE+'.guard.json',
       'common_subset_cone_probe.py','common-subset-cone-probe.json']
records=[]
for rel in files:
    src=LIVE/rel;dst=ROOT/'supplied'/rel;data=src.read_bytes()
    digest=hashlib.sha256(data).hexdigest()
    if rel==MODULE+'.lean':assert digest==SHA
    assert not dst.exists();dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
    records.append(dict(source=str(src),frozen=dst.relative_to(ROOT).as_posix(),sha256=digest,bytes=len(data)))
(ROOT/'source-manifest.json').write_text(json.dumps(dict(files=records),indent=2)+'\n',encoding='utf-8')
old=ROOT.parent/'root-clock-review/replay_review.py'
s=old.read_text(encoding='utf-8')
start=s.index('ORDER=');end=s.index('ap=argparse.ArgumentParser',start)
s=s[:start]+"ORDER=['"+MODULE+"']\nHEADS={}\n"+s[end:]
s=s.replace('all nine custom modules','the supplied 48-constant cyclic diagnostic')
s=s.replace("default=ROOT/'published'","default=ROOT/'supplied'")
s=s.replace("[published/'work'/(module+'.lean'),published/'work/dependencies'/(module+'.lean')]","[published/(module+'.lean')]")
s=s.replace("published/'work/formal'","published/'formal'")
s=s.replace("published_commit='64197054b1e4f5b768a624c16bd3c1db0555f3cb'","supplied_source_sha256='"+SHA+"'")
s=s.replace("    env=dict(os.environ", "    assert custom['"+MODULE+"']=='"+SHA+"'\n    env=dict(os.environ")
(ROOT/'replay_review.py').write_text(s,encoding='utf-8')
print(json.dumps(dict(frozen=len(records),source_sha256=SHA,helper_provenance=str(old))))
