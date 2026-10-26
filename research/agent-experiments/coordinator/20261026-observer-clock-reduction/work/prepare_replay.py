from pathlib import Path
r=Path(__file__).resolve().parent;p=r/'replay.py'
s=p.read_text(encoding='utf-8')
if "HEADS['Rule30OrClockObserverResearch']" not in s:
    s=s.replace('assert module in HEADS',"HEADS['Rule30OrClockObserverResearch']=['shift_flag','older_recovered','hidden_difference_impossible','or_pair_injective_of_anti','actual_or_clock_observer','plateau_local_counterexample']\nassert module in HEADS")
s=s.replace("'actual_or_clock_observer']","'actual_or_clock_observer','plateau_local_counterexample']")
p.write_text(s,encoding='utf-8')
