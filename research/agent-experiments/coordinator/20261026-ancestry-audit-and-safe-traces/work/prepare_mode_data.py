from pathlib import Path
import ast,hashlib,json,shutil
r=Path(__file__).resolve().parent
source=r.parent/'mode-inverse-20261026T1216/mode_coordinates.py'
text=source.read_text(encoding='utf-8');tree=ast.parse(text)
node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='data_for')
segment=ast.get_source_segment(text,node)
(r/'mode_samples.py').write_text('from mode_data import states_graph,rotate,audit,C,integral\n\n'+segment+'\n',encoding='utf-8')
original=r.parent/'jet-mask-20261026T0907/gf2_block.py'
shutil.copyfile(original,r/'gf2_block.py')
meta={'data_for_original_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
      'extracted_function_sha256':hashlib.sha256(segment.encode()).hexdigest(),
      'gf2_block_original_sha256':hashlib.sha256(original.read_bytes()).hexdigest()}
(r/'mode-data-source.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta))
