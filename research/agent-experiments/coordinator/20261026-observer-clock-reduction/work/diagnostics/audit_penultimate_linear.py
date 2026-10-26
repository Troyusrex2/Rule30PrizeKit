from pathlib import Path
import runpy,sys
r=Path(__file__).resolve().parent
sys.argv=[str(r/'audit_linear_decoder.py'),'2']
runpy.run_path(str(r/'audit_linear_decoder.py'),run_name='__main__')
