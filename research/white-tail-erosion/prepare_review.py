"""Freeze a checked review artifact; never submit or change the notebook."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    names = ['source-manifest.json', 'standalone-evidence/report.json',
             'white-tail-erosion-essay.nb.verification.json',
             'white-tail-erosion-essay.nb.inspection.json', 'notebook-build-timing.json']
    data = {}
    for name in names:
        path = HERE / name
        data[name] = json.loads(path.read_text(encoding='utf-8'))
        path.write_text(json.dumps(data[name], indent=2)+'\n', encoding='utf-8', newline='\n')
    source, check, verification, inspection, timing = [data[n] for n in names]
    config = HERE / 'notebook-config.json'
    config.write_text(json.dumps(json.loads(config.read_text()), indent=2)+'\n',
                      encoding='utf-8', newline='\n')
    assert check['verdict'] == 'pass' and check['check']['replay']['ok']
    assert check['check']['replay']['constants'] == 182
    assert check['source_sha256'] == source['embedded_source_sha256']
    assert verification['NotebookEvaluated'] and verification['LeanKernelChecksPassed']
    assert verification['EmbeddedSourceMatched'] and verification['KernelReplayedDeclarations'] == 182
    assert inspection['SavedNotebookSourceRoundTripPassed']
    assert inspection['SavedIndependentControlsPassed'] and inspection['MessageCells'] == 0
    assert inspection['FigurePNGExportsSucceeded'] and not timing['UseCache']
    notebook = HERE / 'white-tail-erosion-essay.nb'
    assert hashlib.sha256(notebook.read_bytes()).hexdigest() == inspection['NotebookSHA256']
    assert hashlib.sha256((HERE / 'Rule30WhiteTailErosionStandalone.lean').read_bytes()).hexdigest() == verification['StandaloneFileSHA256']
    assert all(not d.get('PrizeAPISubmitted', d.get('prize_api_submitted', False)) for d in data.values())
    files = sorted(p for p in HERE.rglob('*') if p.is_file() and
                   p.name != 'review-manifest.json' and p.suffix not in ('.log', '.pyc')
                   and '__pycache__' not in p.parts)
    manifest = {'review_ready': True, 'authors': 'Troy Lowry; OpenAI Codex (GPT-6)',
                'claim': 'partial', 'full_problem_solved': False,
                'prize_api_submitted': False, 'human_approval_pending': True,
                'reference_commit': source['reference_commit'],
                'headlines': source['headlines'],
                'files': {p.relative_to(HERE).as_posix(): {'bytes': p.stat().st_size,
                           'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in files}}
    (HERE / 'review-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n',
                                             encoding='utf-8', newline='\n')
    print(json.dumps({'review_ready': True, 'files': len(files),
                      'notebook_sha256': inspection['NotebookSHA256'],
                      'prize_api_submitted': False}))


if __name__ == '__main__':
    main()
