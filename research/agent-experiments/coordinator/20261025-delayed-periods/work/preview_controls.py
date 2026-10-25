from pathlib import Path
import json,hashlib
root=Path(__file__).resolve().parent
data=json.loads((root/'essay-preview-data.json').read_text());assert len(data)==5
checks=0
for j,observed in enumerate(data):
    mu=8*j+8;width=mu+4;mask=(1<<width)-1
    cur=sum(int(t==8*j+5 or t%4!=1)<<t for t in range(width));prev=0
    expected=[0,cur&1]
    for d in range(2,161):
        shifted=(cur>>1)|((cur>>mu&1)<<(width-1))
        prev,cur=cur,(shifted^(cur|prev))&mask
        expected.append(cur&1)
    assert observed==expected,j
    checks+=len(expected)
assert checks==805
source=(root/'Rule30Submission.lean').read_bytes()
assert source==(root/'notebook-extracted.lean').read_bytes()
build=json.loads((root/'essay-build.json').read_text());fresh=json.loads((root/'essay-fresh-check.json').read_text())
assert build['sourceSHA256']==fresh['sourceSHA256']==hashlib.sha256(source).hexdigest()
assert build['notebookSHA256']==fresh['notebookSHA256']==hashlib.sha256((root/'delayed-defect-essay.nb').read_bytes()).hexdigest()
assert fresh['freshKernelEvaluation'] and fresh['kernelCheckSuccess'] and fresh['sourceRoundTrip']
assert build['kernelCheckSuccess'] and fresh['singleSeedPrefixControl'] and fresh['inputCells']==7
assert not build['submitted'] and not fresh['submitted']
report={'pass':True,'independent_preview_cells':checks,'exact_embedded_source_bytes':True,
        'fresh_notebook_kernel_replay':True,'submitted':False}
(root/'preview-controls.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report))
