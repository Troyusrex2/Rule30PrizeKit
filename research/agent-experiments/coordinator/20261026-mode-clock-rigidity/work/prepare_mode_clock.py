from pathlib import Path
r=Path(__file__).resolve().parent;p=r/'replay.py';s=p.read_text(encoding='utf-8')
line="HEADS['Rule30ModeClockRigidityResearch']=['mode_readout_no_half_clock','actual_lower_readout_no_half_clock']\n"
if line not in s:s=s.replace('assert module in HEADS',line+'assert module in HEADS')
p.write_text(s,encoding='utf-8')
