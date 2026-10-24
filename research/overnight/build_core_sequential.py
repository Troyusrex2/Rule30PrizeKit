"""Build the standalone core catalog in dependency order to bound peak memory."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('audit', HERE / 'audit_contributions.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lake', required=True)
    args = ap.parse_args()
    project = ROOT / 'lean'
    evidence = HERE / 'core-evidence'
    evidence.mkdir(parents=True, exist_ok=True)
    visited, order = set(), []

    def visit(module):
        if module in visited:
            return
        path = project / Path(module.replace('.', '/')).with_suffix('.lean')
        if not path.exists():
            return  # Lean's own modules are trusted toolchain imports.
        visited.add(module)
        for dependency in re.findall(r'^(?:public )?import ([\w.]+)',
                                     path.read_text(encoding='utf-8'), re.MULTILINE):
            visit(dependency)
        order.append(module)

    visit('Ruliology')
    report = {'verdict': 'running', 'standalone_core_catalog_build': False,
              'parallel_cold_build_resource_guard_triggered': True,
              'full_problem_claim': False, 'explicit_build_target_count': len(order), 'completed': []}
    target = HERE / 'core-build.json'
    for module in order:
        seconds = audit.run([args.lake, 'build', module], project,
                            evidence / (module + '.build.log'))
        report['completed'].append({'module': module, 'seconds': round(seconds, 3)})
        target.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
        print(json.dumps({'built': module, 'completed': len(report['completed']),
                          'total': len(order)}), flush=True)
    report.update(verdict='pass', standalone_core_catalog_build=True,
                  root_source_sha256=hashlib.sha256((project / 'Ruliology.lean').read_bytes()).hexdigest())
    target.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
