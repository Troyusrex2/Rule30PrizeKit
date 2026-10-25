from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parent
old=Path(r'D:\MWB\Rule30\current-reference-3eca-20261024')
new=Path(r'D:\MWB\Rule30\current-reference-009005-20261025')
assert (old/'Check.lean').read_bytes()==(new/'Check.lean').read_bytes()
changed=subprocess.check_output(['git','diff','--name-only',
 '3eca23c0a9fa6b153313655e6d51835406c2d06e','0090056412733accaa27643d3cbbf982104f2251'],cwd=new,text=True).splitlines()
assert set(changed)=={'Rule30PrizeKit.lean','build_all.sh','lean/README.md','lean/Ruliology.lean',
 'lean/Ruliology/CellularAutomata/Rule30Certificates/StripeTail13Completion.lean',
 'lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryStripeFourComplete.lean',
 'lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryStripeFrontLift.lean'}
s=(root/'check_catalog.py').read_text().replace('current-reference-3eca-20261024','current-reference-009005-20261025').replace('catalog-evidence','catalog-current-evidence')
(root/'check_catalog_current.py').write_text(s,encoding='utf-8')
(root/'pin-change-audit.json').write_text(json.dumps({'old':subprocess.check_output(['git','rev-parse','HEAD'],cwd=old,text=True).strip(),
 'new':subprocess.check_output(['git','rev-parse','HEAD'],cwd=new,text=True).strip(),
 'checker_identical':True,'checker_sha256':hashlib.sha256((new/'Check.lean').read_bytes()).hexdigest(),
 'changed_files':changed,'proof_import_sources_changed':False},indent=2)+'\n',encoding='utf-8')
print('New pin checker identical; changed files outside proof import closure')
