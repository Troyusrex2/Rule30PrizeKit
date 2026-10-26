"""Run this response's experiment in a NEW output directory, with bounded resources."""
import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path
import psutil

p = argparse.ArgumentParser()
p.add_argument('--output', required=True, type=Path)
args = p.parse_args()
out = args.output.resolve()
out.mkdir(parents=True, exist_ok=False)
script = Path(__file__).with_name('experiment.py')
started = time.monotonic()
limit = 8*1024**3
floor = 2*1024**3
record = {'runtime_limit_seconds': 300, 'owned_tree_rss_limit_bytes': limit,
          'minimum_available_memory_bytes': floor, 'python': sys.version.split()[0],
          'psutil': psutil.__version__,
          'source_sha256': hashlib.sha256(script.read_bytes()).hexdigest(),
          'solver': 'none; exact integer/Boolean arithmetic', 'status': 'unknown'}
proc = None
peak = 0
try:
    if psutil.virtual_memory().available < floor:
        raise RuntimeError('insufficient available memory; experiment not run')
    with (out/'experiment.run.log').open('w',encoding='utf-8') as log:
        proc = subprocess.Popen([sys.executable, str(script), str(out)],
                                stdout=log, stderr=subprocess.STDOUT)
        owner = psutil.Process(proc.pid)
        while proc.poll() is None:
            tree = [owner]+owner.children(recursive=True)
            rss = 0
            for child in tree:
                try: rss += child.memory_info().rss
                except psutil.NoSuchProcess: pass
            peak = max(peak, rss)
            if rss > limit or psutil.virtual_memory().available < floor or time.monotonic()-started > 300:
                raise RuntimeError('owned job resource guard reached; no pass claimed')
            time.sleep(.1)
    record['exit_code'] = proc.returncode
    if proc.returncode != 0: raise RuntimeError('experiment failed; inspect log')
    results = json.loads((out/'results.json').read_text())
    assert results['status']=='completed_exact_finite_computation'
    assert results['center_sha256']==hashlib.sha256((out/'center.bits').read_bytes()).hexdigest()
    record['status']='completed_exact_finite_computation'
except Exception as exc:
    record['error']=str(exc)
    raise
finally:
    if proc is not None and proc.poll() is None:
        # Only processes spawned by this invocation are eligible for termination.
        for child in reversed([owner]+owner.children(recursive=True)):
            try: child.kill()
            except psutil.NoSuchProcess: pass
        proc.wait()
    record['guard_seconds']=round(time.monotonic()-started,6)
    record['peak_sampled_owned_rss_bytes']=peak
    (out/'run-metadata.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,indent=2))
