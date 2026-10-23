"""Synchronize the standalone proof and its one embedded Wolfram string."""
import json
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[1]
source=(PROJECT/'lean/Ruliology/CellularAutomata/Rule30ColumnSeparationResearch.lean').read_text(encoding='utf-8')
source=source.removeprefix('module\n').replace('public import ','import ').replace('@[expose] public section','')
source=source.replace('namespace Ruliology.CellularAutomata.Rule30ColumnSeparationResearch',
                      'open Ruliology.CellularAutomata\n\nnamespace Rule30Submission')
source=source.replace('end Ruliology.CellularAutomata.Rule30ColumnSeparationResearch','end Rule30Submission')
(HERE/'Rule30ColumnSeparationStandalone.lean').write_text(source,encoding='utf-8',newline='\n')
essay=HERE/'column-separation-essay.md'
text=essay.read_text(encoding='utf-8')
pattern=r'LeanImportString\["(?:\\.|[^"\\])*"'
replacement='LeanImportString['+json.dumps('import Rule30PrizeKit\n'+source,ensure_ascii=False)
text,count=re.subn(pattern,lambda _:replacement,text)
assert count==1,'Expected one embedded source literal'
essay.write_text(text,encoding='utf-8',newline='\n')
print('Synchronized the standalone proof and its exact embedded source')
