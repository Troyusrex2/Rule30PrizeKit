"""Guard the complete umbrella build after the four individual checks."""
import importlib.util,json
from core import HERE,BASE,REPO

def main():
    project=BASE/'front-tools-catalog-20261024';lake=BASE/'toolchain/lean-4.35.0-windows/bin/lake.exe'
    out=HERE/'front-tools-catalog-evidence'
    prior=json.loads((out/'report.json').read_text(encoding='utf-8'));assert prior['verdict']=='pass'
    spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
    guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
    elapsed=guard.guarded([str(lake),'build','Ruliology'],project,out/'Ruliology.build.log')
    result={'verdict':'pass','target':'Ruliology','seconds':elapsed,'full_problem_solved':False}
    (out/'umbrella-build.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(result,flush=True)

if __name__=='__main__':main()
