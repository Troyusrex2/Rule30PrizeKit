"""Test whether the low-class finite-band conjecture needs initial subset."""
from pathlib import Path
source=Path(__file__).with_name('prefix_class_probe.py').read_text(encoding='utf-8')
source=source.replace('if not cls0(b0):continue','if False:continue')
source=source.replace("'younger_low_class_zero_required':True", "'younger_low_class_zero_required':False")
source=source.replace("'initial_subset_required':True", "'initial_subset_required':False")
source=source.replace('positions=[j for j in range(L) if delta>>j&1]', 'positions=list(range(L))')
source=source.replace("'prefix-class-probe.json'","'prefix-unrestricted-probe.json'")
exec(compile(source,str(Path(__file__).with_name('prefix_class_probe.py')),'exec'))
