"""Run only an explicitly named local script under the existing job guard."""
from pathlib import Path
import sys
from core import guarded_script, HERE
script=Path(sys.argv[1]).resolve()
suffix=('-'+'-'.join(sys.argv[2:]).replace('--','')) if len(sys.argv)>2 else ''
log=HERE/(script.stem+suffix+'.run.log')
print({'script':str(script),'log':str(log)},flush=True)
seconds=guarded_script(script,log,sys.argv[2:])
print({'status':'passed','seconds':seconds,'log':str(log)},flush=True)
