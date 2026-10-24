from pathlib import Path
import argparse,importlib.util,shutil
from core import HERE,REPO
spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
parser=argparse.ArgumentParser()
parser.add_argument('--wolframscript',default=shutil.which('wolframscript') or 'C:/Program Files/Wolfram Research/Wolfram Engine/15.0/wolframscript.exe')
args=parser.parse_args();engine=Path(args.wolframscript)
seconds=guard.guarded([str(engine),'-file',str(HERE/'wolfram_controls.wl')],HERE,HERE/'wolfram-controls.log')
print({'status':'pass','seconds':seconds})
