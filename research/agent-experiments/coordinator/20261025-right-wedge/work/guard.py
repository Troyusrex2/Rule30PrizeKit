"""Run one owned research job; never signal any unrelated process."""
import json, os, subprocess, sys, time
from pathlib import Path
import psutil

root = Path(__file__).resolve().parent
label = Path(sys.argv[1]).stem
if label in ['replay','replay_with_reference_imports'] and len(sys.argv)>2:
    assert sys.argv[2].isidentifier()
    label += '-' + sys.argv[2]
log = root / 'evidence' / (label + '.log')
log.parent.mkdir(exist_ok=True)
start = time.monotonic()
peak = 0
minimum_available = psutil.virtual_memory().available
stop = None
command = [sys.executable, '-B', str(root / sys.argv[1]), *sys.argv[2:]]
environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONUTF8='1')
if minimum_available < 2 * 1024**3:
    raise SystemExit('Insufficient system available memory before launch')
with log.open('w', encoding='utf-8') as stream:
    process = subprocess.Popen(command, cwd=root, env=environment, stdout=stream, stderr=subprocess.STDOUT)
    owned = psutil.Process(process.pid)
    while process.poll() is None:
        members = [owned]
        try:
            members += owned.children(recursive=True)
        except psutil.NoSuchProcess:
            pass
        rss = 0
        for member in members:
            try:
                rss += member.memory_info().rss
            except psutil.NoSuchProcess:
                pass
        peak = max(peak, rss)
        available = psutil.virtual_memory().available
        minimum_available = min(minimum_available, available)
        if time.monotonic() - start > 300:
            stop = 'wall_time'
        elif rss > 8 * 1024**3:
            stop = 'owned_tree_memory'
        elif available < 2 * 1024**3:
            stop = 'system_available_memory'
        if stop:
            for member in reversed(members):
                try:
                    member.kill()
                except psutil.NoSuchProcess:
                    pass
            break
        time.sleep(0.1)
    code = process.wait(timeout=10)
result = {'command': command, 'exit_code': code, 'guard_stop': stop,
          'elapsed_seconds': time.monotonic()-start, 'peak_owned_rss_bytes': peak,
          'minimum_system_available_bytes': minimum_available,
          'limits': {'seconds': 300, 'owned_rss_gib': 8, 'minimum_system_available_gib': 2},
          'sampling_seconds': 0.1}
(root / 'evidence' / (label + '.guard.json')).write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(json.dumps(result))
print(log.read_text(encoding='utf-8')[-4000:].encode('ascii','backslashreplace').decode('ascii'))
raise SystemExit(code if code else (1 if stop else 0))
