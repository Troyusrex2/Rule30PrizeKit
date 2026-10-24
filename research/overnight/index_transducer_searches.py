"""Index numerical experiments without promoting them to Lean results."""
import hashlib
import json
from pathlib import Path

here = Path(__file__).resolve().parent
patterns = ['transducer-potential-*.json', 'cycle-transducer-*.json', 'controlled-transducer-*.json',
            'position-transducer-*.json', 'front-transducer-*.json', 'front-distance-*.json',
            'history-transducer-*.json', 'inversion-potential-*.json', 'pair-containment-potential-*.json',
            'lag-correlated-potential-*.json', 'stripe-prefix-dfa-*.json']
entries = []
for path in sorted({p for pattern in patterns for p in here.glob(pattern)}):
    report = json.loads(path.read_text(encoding='utf-8'))
    entry = {'report': path.name, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
             'status': report.get('status'), 'message': report.get('message', report.get('reason_unknown')),
             'exact_arithmetic_LP_refutation': report.get('farkas', {}).get('exact_arithmetic_checked', False),
             'Lean_verified': False}
    for key in ['radius', 'degree', 'exact_retained_history', 'head_history', 'controller_length',
                'front_parity', 'signed_weights_with_graph_lower_bound', 'seconds', 'actual_elapsed_seconds',
                'reward_mode', 'auxiliary_graph_degree', 'signed_weights_with_uniform_graph_lower_bound',
                'lag', 'stride', 'require_alternation', 'local_pattern_length', 'graph_window',
                'prefix_dfa_states', 'tracks_prefix_ones_parity', 'pattern_length',
                'signed_weights_with_accepted_path_lower_bound']:
        if key in report: entry[key] = report[key]
    entries.append(entry)
result = {'Lean_verified_results': False, 'prize_problem_proved': False, 'entries': entries}
(here/'transducer-search-index.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps({'indexed_experiments': len(entries), 'Lean_verified_results': False}))
