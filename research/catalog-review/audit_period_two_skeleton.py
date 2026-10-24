"""Replay Quint/Gemini's public period-two skeleton, without editing its proof.

This is an independent audit of another author's partial result. It adds no
proof of Q01 or of the prize statement, and makes no new submission.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import urllib.request

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'overnight'))
from audit_contributions import run


SUBMISSION = 'R30-20261024-1e1b3b'
SOURCE_URL = ('https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/file?id='
              + SUBMISSION + '&kind=lean')
SOURCE_SHA256 = 'acf1d4bbb1ec1b58ae32e45d61f99129b8b96f414b734041de21fbc3e3d02f73'
REFERENCE = '2f63afda261888e04ec57237290e723190914a1d'
MODULE = 'Rule30ExternalPeriodTwoSkeletonReview'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project', type=Path, required=True)
    ap.add_argument('--lake', required=True)
    args = ap.parse_args()
    project = args.project.resolve()
    evidence = Path(__file__).with_name('period-two-skeleton-audit')
    evidence.mkdir(exist_ok=True)
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project,
                                   text=True).strip()
    if head != REFERENCE:
        raise RuntimeError('Use the exact reference checkout recorded by this audit')
    checker = (project / 'Check.lean').read_bytes().replace(b'\r\n', b'\n')
    expected = subprocess.check_output(['git', 'show', 'HEAD:Check.lean'], cwd=project)
    if checker != expected:
        raise RuntimeError('Official checker differs from reference source')
    raw = urllib.request.urlopen(SOURCE_URL, timeout=30).read()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA256:
        raise RuntimeError('Public proof source changed; inspect before auditing it')
    # The published UTF-8 source is compiled byte for byte, including its imports.
    raw.decode('utf-8')
    target = project / (MODULE + '.lean')
    if target.exists() and target.read_bytes() != raw:
        raise RuntimeError('Refusing to overwrite different local proof source')
    target.write_bytes(raw)
    metadata = json.load(urllib.request.urlopen(
        'https://www.wolframcloud.com/obj/rule-30-prize/Agents/submissions.json', timeout=30))
    entry = next(e for e in metadata['entries'] if e['id'] == SUBMISSION)
    headlines = entry['headlines']
    build_seconds = run([args.lake, 'build', 'Rule30PrizeKit'], project,
                        evidence / 'dependencies.log')
    artifact = project / '.lake/build/lib/lean' / (MODULE + '.olean')
    compile_seconds = run([args.lake, 'env', 'lean', '-o', str(artifact), str(target)],
                          project, evidence / 'compile.log')
    argv = [args.lake, 'env', 'lean', '--run', 'Check.lean', MODULE, '--claim', 'partial']
    for headline in headlines:
        argv += ['--headline', headline]
    check_log = evidence / 'check.log'
    check_seconds = run(argv, project, check_log)
    data = json.loads([s for s in check_log.read_text(encoding='utf-8').splitlines()
                       if s.startswith('{')][-1])
    assert data['verdict'] == 'pass' and data['replay']['ok'] and not data['newAxioms']
    assert all(h['ok'] for h in data['headlines'])
    assert target.read_bytes() == raw
    assert (project / 'Check.lean').read_bytes().replace(b'\r\n', b'\n') == expected
    report = {'verdict': 'pass', 'submission': SUBMISSION, 'title': entry['title'],
              'upstream_authors': entry['authors'], 'upstream_agent': entry['agent'],
              'source_url': SOURCE_URL, 'source_sha256': SOURCE_SHA256,
              'source_adapted': False, 'checker_modified': False,
              'reference_commit': REFERENCE, 'module': MODULE,
              'official_status_at_fetch': entry['status'],
              'official_tags_at_fetch': entry.get('tags', []),
              'scope': 'Conditional forced identities through column -10 and '
                       'conditional nonperiodicity of selected free traces',
              'q01_proved': False, 'problem1_proved': False,
              'authorship_or_priority_claim': False,
              'warm_dependency_build_seconds': round(build_seconds, 3),
              'compile_seconds': round(compile_seconds, 3),
              'check_seconds': round(check_seconds, 3), 'check': data}
    (evidence / 'report.json').write_text(json.dumps(report, indent=2) + '\n',
                                        encoding='utf-8', newline='\n')
    print(json.dumps({'verdict': 'pass', 'constants': data['replay']['constants'],
                      'headlines': len(data['headlines']), 'submission': SUBMISSION}),
          flush=True)


if __name__ == '__main__':
    main()
