"""Recover per-module guard records after fixing a shared log-name collision."""
from pathlib import Path
import json,subprocess,sys
root=Path(__file__).resolve().parent
jobs=[('Rule30RoundTwoDrivenPrefixResearch',['trace_sound']),
      ('Rule30RoundTwoChargeTwoEntryResearch',['right_finite','trace_checked','entry_ether','entry_wall','right_col1_after','free_stream']),
      ('Rule30RoundTwoChargeTwoThetaResearch',['table_rule','model_rule','recon_model_pair','theta_left','psi_left']),
      ('Rule30RoundTwoChargeTwoResearch',['left_period','black_chunks','zeros_even','coupled_scale_counts','coefficient_two_false','minimum_integer_coefficient'])]
for name,heads in jobs:
    r=subprocess.run([sys.executable,'-B','guard.py','replay_with_reference_imports.py',name,*heads],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=True)
    (root/'evidence'/('final-'+name+'.stdout.log')).write_bytes(r.stdout)
    report=json.loads((root/'evidence'/name/'report.json').read_text())
    guard=json.loads((root/'evidence'/('replay_with_reference_imports-'+name+'.guard.json')).read_text())
    assert guard['exit_code']==0 and guard['guard_stop'] is None
    print(json.dumps({'module':name,'check':report['check']['verdict'],'replayed':report['check']['replay']['constants'],'seconds':guard['elapsed_seconds']}),flush=True)
