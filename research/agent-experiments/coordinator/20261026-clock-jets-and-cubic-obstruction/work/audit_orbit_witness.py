from pathlib import Path
import sys,runpy
r=Path(__file__).resolve().parent
sys.argv=[str(r/'audit_cubic_witness.py'),'cubic-negative-witness-orbit-min.json','orbit-witness-audit.json']
runpy.run_path(str(r/'audit_cubic_witness.py'),run_name='__main__')
