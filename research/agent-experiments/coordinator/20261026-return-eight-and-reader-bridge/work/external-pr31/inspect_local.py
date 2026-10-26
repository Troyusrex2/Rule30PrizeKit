"""Record source comparison and scope facts without changing public source bytes."""
from pathlib import Path
import difflib,json,subprocess,hashlib
root=Path(__file__).resolve().parent;repo=Path('D:/MWB/Rule30/overnight-20261024')
pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
old=subprocess.check_output(['git','-C',str(repo),'show',pin+':lean/Ruliology/CellularAutomata/Rule30PaddedWords.lean'])
new=(root/'Rule30PaddedWords.lean').read_bytes()
(root/'padded-words-versus-official.diff').write_text(''.join(difflib.unified_diff(old.decode('utf-8').splitlines(True),new.decode('utf-8').splitlines(True),fromfile='official5473/Rule30PaddedWords.lean',tofile='public88dd/Rule30PaddedWords.lean')),encoding='utf-8')
source=json.loads((root/'public-source.json').read_bytes())
print(json.dumps({'exact_sources':source['sources'],'padded_diff_lines':len((root/'padded-words-versus-official.diff').read_text(encoding='utf-8').splitlines())},indent=2))
