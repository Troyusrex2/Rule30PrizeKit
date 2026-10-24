"""Bind the locally checked review artifact to its exact notebook and sources.

Use --figures-reviewed after visually checking the two exported data figures.
No submission API is called.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent

def read(name):
    return json.loads((HERE/name).read_text(encoding='utf-8'))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--figures-reviewed',action='store_true',required=True)
    parser.parse_args()
    manifest=read('source-manifest.json')
    cli=read('standalone-evidence/report.json')
    verification=read('stripe-meeting-essay.nb.verification.json')
    inspection=read('stripe-meeting-essay.nb.inspection.json')
    reading=read('notebook-read-summary.json')
    notebook=HERE/'stripe-meeting-essay.nb'
    assert cli['verdict']=='pass' and cli['check']['replay']['ok']
    assert not cli['check']['newAxioms'] and all(h['ok'] for h in cli['check']['headlines'])
    assert verification['NotebookEvaluated'] and verification['LeanKernelChecksPassed']
    assert verification['AllHeadlineAxiomsStandard'] and verification['EmbeddedSourceMatched']
    assert verification['StandaloneFileSHA256']==manifest['standalone_body_sha256']
    assert cli['source_sha256']==manifest['embedded_source_sha256']
    assert inspection['SavedNotebookSourceRoundTripPassed'] and inspection['SavedIndependentControlsPassed']
    assert inspection['MessageCells']==0 and inspection['FigurePNGExportsSucceeded']
    assert reading['ReadNotebookSucceeded'] and reading['KernelCheckedOutputVisible'] and reading['LeanEnvironmentOutputVisible']
    digest=hashlib.sha256(notebook.read_bytes()).hexdigest()
    assert digest==inspection['NotebookSHA256']
    report={'title':'Stripe-related Rule 30 rows share their entire center trace',
        'authors':'Troy Lowry; OpenAI Codex','catalog_pr':'https://github.com/WolframInstitute/Rule30PrizeKit/pull/13',
        'notebook_sha256':digest,'notebook_bytes':notebook.stat().st_size,'source_manifest':manifest,
        'standalone_verdict':cli['verdict'],'standalone_replayed_declarations':cli['check']['replay']['constants'],
        'notebook_replayed_declarations':verification['KernelReplayedDeclarations'],
        'independent_builtin_pairs':inspection['BuiltinRule30Pairs'],
        'independent_scalar_cells':inspection['ScalarCellsCompared'],
        'saved_source_roundtrip_passed':True,'saved_message_cells':0,'read_notebook_succeeded':True,
        'figures_visually_checked':True,'figures':[{'name':name,'sha256':hashlib.sha256((HERE/name).read_bytes()).hexdigest()}
            for name in ['figure-seed.png','figure-stripe-difference.png']],
        'full_problem_solved':False,'trace_completeness_proved':False,
        'prize_api_submitted':False,'human_approval_for_this_new_essay_received':False}
    (HERE/'review-manifest.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'review_artifact_checked':True,'notebook_sha256':digest,'notebook_bytes':notebook.stat().st_size,
                      'prize_api_submitted':False}))

if __name__=='__main__':main()
