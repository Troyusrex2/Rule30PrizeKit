from pathlib import Path
r=Path(__file__).resolve().parent;p=r/'replay.py';s=p.read_text(encoding='utf-8')
line="HEADS['Rule30EvenModeRigidityResearch']=['constant_readout_driver','even_constant_mode_impossible','actual_even_plateau_readout','actual_even_plateau_or_no_half_period','constant_or_forces_double_period','actual_even_plateau_or_clock_rigidity']\n"
import re
s=re.sub(r"HEADS\['Rule30EvenModeRigidityResearch'\]=[^\n]*\n",'',s)
s=s.replace('assert module in HEADS',line+'assert module in HEADS')
p.write_text(s,encoding='utf-8')
