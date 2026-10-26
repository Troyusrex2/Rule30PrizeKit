from pathlib import Path
r=Path(__file__).resolve().parent;p=r/'replay.py'
s=p.read_text(encoding='utf-8')
if "HEADS['Rule30ClockJetResearch']" not in s:
    s=s.replace('assert module in HEADS',"HEADS['Rule30ClockJetResearch']=['shift_difference_step','shift_or_mask','shift_or_difference','plateau_or_double','actual_plateau_jet']\nassert module in HEADS")
p.write_text(s,encoding='utf-8')
