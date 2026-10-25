"""Check whether only the older row's low-three-bit class is sufficient."""
from pathlib import Path
source=Path(__file__).with_name('prefix_class_probe.py').read_text(encoding='utf-8')
source=source.replace('if not cls0(b0):continue','if False:continue')
source=source.replace("'younger_low_class_zero_required':True", "'younger_low_class_zero_required':False")
source=source.replace("'prefix-class-probe.json'","'prefix-a-only-probe.json'")
exec(compile(source,str(Path(__file__).with_name('prefix_class_probe.py')),'exec'))
