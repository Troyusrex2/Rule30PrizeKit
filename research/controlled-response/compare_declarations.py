"""Compare named declarations after the documented standalone adaptation."""
import ast
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    tree = ast.parse((HERE/'generate_essay.py').read_text(encoding='utf-8'))
    modules = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
                   and any(isinstance(t, ast.Name) and t.id == 'modules' for t in n.targets))
    catalog = json.loads((HERE/'catalog-verification.json').read_text())
    standalone = json.loads((HERE/'standalone-verification.json').read_text())
    assert catalog['verdict'] == standalone['verdict'] == 'pass'
    assert len(catalog['modules']) == len(modules)
    names = set()
    for module in catalog['modules']:
        stem = module['module'].split('.')[-1]
        for declaration in module['check']['declared']:
            name = declaration['name']
            for old, new in modules.items():
                name = name.replace('Ruliology.CellularAutomata.'+old, 'Rule30Submission.'+new)
            names.add(name)
    combined = {d['name'] for d in standalone['check']['declared']}
    def auxiliary(name):
        return any(piece.startswith(('match_', 'eq_')) for piece in name.split('.'))
    semantic = {n for n in names if not auxiliary(n)}
    other = {n for n in combined if not auxiliary(n)}
    assert semantic == other, (sorted(semantic-other), sorted(other-semantic))
    report = {'all_named_nonmatcher_declarations_preserved': True,
              'named_declarations_compared': len(semantic),
              'catalog_replay_sum': sum(m['check']['replay']['constants'] for m in catalog['modules']),
              'combined_replay_constants': standalone['check']['replay']['constants'],
              'catalog_only_auxiliary_names': sorted(names-combined),
              'combined_only_auxiliary_names': sorted(combined-names),
              'full_problem_claim': False}
    assert all(auxiliary(n) for n in (names ^ combined))
    (HERE/'declaration-comparison.json').write_text(json.dumps(report, indent=2)+'\n',
                                                  encoding='utf-8', newline='\n')
    print(json.dumps({k:v for k,v in report.items() if not isinstance(v,list)}))


if __name__ == '__main__':
    main()
