"""Corrected cone bound; preserve the failed original run as evidence."""
from pathlib import Path
source = Path(__file__).with_name('dyadic_pulse_probe.py').read_text(encoding='utf-8')
source = source.replace('U-2)', '(U-3)//2)')
source = source.replace("'dyadic-pulse-probe.json'", "'dyadic-pulse-checked.json'")
exec(compile(source, str(Path(__file__).with_name('dyadic_pulse_probe.py')), 'exec'))
