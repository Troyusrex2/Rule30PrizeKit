"""Independent Boolean/literal audit of the closed graph and finite supports."""
from collections import deque
from itertools import product
from pathlib import Path
import hashlib
import json


def unpack(s):
    return tuple(bool(s & (1 << i)) for i in range(3))


def encode(a, b, h):
    return int(a) + 2 * int(b) + 4 * int(h)


def common(x, y):
    a, b, h = unpack(x)
    aa, bb, hh = unpack(y)
    return ((a != b) and hh) == (h and (aa != bb))


def invalid(s):
    a, b, h = unpack(s)
    return h and a == b


def literal_output(x, y, z):
    a0, b0, h0 = unpack(x)
    a1, b1, h1 = unpack(y)
    a2, b2, h2 = unpack(z)
    # Independent Rule30 truth table for both actual coefficients.
    table = (False, True, True, True, True, False, False, False)
    aa = table[4 * int(a2) + 2 * int(a1) + int(a0)]
    bb = table[4 * int(b2) + 2 * int(b1) + int(b0)]
    hh = h2 != (((not b0) and h1) != ((not a1) and h0))
    return encode(aa, bb, hh)


def next_state(state, s):
    x, y, previous, badin, badout = state
    output = literal_output(x, y, s)
    reject = []
    if not common(y, s):
        reject.append('input_Common')
    if not common(previous, output):
        reject.append('output_Common')
    if reject:
        return None, output, reject
    return [y, s, output, badin or invalid(s), badout or invalid(output)], output, []


def complete(state, tail):
    out = []
    for s in tail:
        state, v, reject = next_state(state, s)
        out.append(v)
        if state is None:
            return {'valid': False, 'outputs': out, 'reasons': reject}
    assert state[0] in (0, 3) and state[1] in (0, 3)
    for s in (0, 3):
        v = literal_output(state[0], state[1], s)
        assert v in (0, 3) and common(state[2], v) and not invalid(v)
    return {'valid': True, 'outputs': out,
            'input_Subset': not state[3], 'output_Subset': not state[4]}


def whole_step(word):
    # Complete finite support, including all radius-two newer output cells.
    padded = [0, 0] + list(word) + [0, 0]
    return [literal_output(*padded[j:j + 3]) for j in range(len(word) + 2)]


def properties(word):
    word = list(word)
    cols = list(zip(*(unpack(s) for s in word))) if word else [(), (), ()]
    nums = [sum(int(b) << j for j, b in enumerate(col)) for col in cols]
    failure = [j for j, s in enumerate(word) if invalid(s)]
    pairs = [j for j in range(len(word)) if not common(word[j], word[j + 1] if j + 1 < len(word) else 0)]
    return {'A': nums[0], 'B': nums[1], 'H': nums[2], 'D': nums[0] ^ nums[1],
            'subset': not failure, 'Subset_failure_positions': failure,
            'common': not pairs, 'Common_failure_pair_starts': pairs,
            'support_checked_through': len(word) - 1}


def main():
    root = Path(__file__).resolve().parent
    cert = json.loads((root / 'certificate.json').read_text())
    nodes = cert['nodes']
    assert len(nodes) == cert['reachable_states'] <= 2048
    assert nodes[0]['state'] == [0, 0, 0, False, False]
    reached = {0}
    queue = deque([0])
    for index, node in enumerate(nodes):
        assert node['id'] == index and len(node['edges']) == 8
        assert node['flush'] == complete(node['state'], (0, 0))
        for s, edge in enumerate(node['edges']):
            target, output, reject = next_state(node['state'], s)
            assert edge['input'] == s and edge['output'] == output
            if target is None:
                assert edge['target'] is None and edge['reject'] == reject
            else:
                assert isinstance(edge['target'], int) and nodes[edge['target']]['state'] == target
    while queue:
        for edge in nodes[queue.popleft()]['edges']:
            t = edge['target']
            if t is not None and t not in reached:
                reached.add(t)
                queue.append(t)
    assert len(reached) == len(nodes)
    white_pairs = set()
    shared_pairs = set()
    valid_shared_completions = 0
    for node in nodes:
        for tail in product((0, 3), repeat=2):
            c = complete(node['state'], tail)
            if c['valid']:
                key = str(int(c['input_Subset'])) + str(int(c['output_Subset']))
                shared_pairs.add(key)
                valid_shared_completions += 1
                if tail == (0, 0):
                    white_pairs.add(key)
    assert sorted(white_pairs) == cert['completed_Subset_pairs']
    controls = {}
    for key, witness in cert['witnesses'].items():
        word = witness['input_symbols']
        state = nodes[0]['state']
        for s in word:
            state, _, reject = next_state(state, s)
            assert state is not None and not reject
        assert state == nodes[witness['end_state']]['state']
        before, after = properties(word), properties(whole_step(word))
        assert before['common'] and after['common']
        assert key == str(int(before['subset'])) + str(int(after['subset']))
        controls[key] = {'input': before, 'output': after,
                         'input_symbols': word, 'output_symbols': whole_step(word)}
    # Explicit requested next rows of the already found forward witness only.
    word = cert['witnesses']['10']['input_symbols']
    followup = []
    first_common_failure = None
    for t in range(9):
        p = properties(word)
        followup.append(dict(time=t, **p))
        if not p['common']:
            first_common_failure = t
            break
        word = whole_step(word)
    result = {
        'status': 'Independent literal audit PASS; forward and backward globally finite-support one-step implications are both false',
        'certificate_sha256': hashlib.sha256((root / 'certificate.json').read_bytes()).hexdigest(),
        'reachable_states': len(nodes), 'all_transitions_checked': 8 * len(nodes),
        'closed_graph_verified': True, 'all_nodes_reachable_verified': True,
        'white_tail_completed_pairs': sorted(white_pairs),
        'shared_tail_completed_pairs': sorted(shared_pairs),
        'shared_tail_flush_choices_per_state': 4,
        'shared_tail_completions_checked': 4 * len(nodes),
        'shared_tail_valid_completions': valid_shared_completions,
        'literal_full_support_controls': controls,
        'forward_witness_followup': followup,
        'forward_first_Common_failure_time': first_common_failure,
        'followup_scope': 'Only the specified forward witness; stop at first Common failure, with hard cap8 if none. No search or extra candidate horizons.',
        'global_tail_bridge': 'After two equal-background symbols with H=0, D=H=0 in every subsequent output for any shared background tail; Common with the final flushed output is automatic.',
        'all_time_Common_claimed': False, 'kernel_checked': False,
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (root / 'audit.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: result[k] for k in ('status', 'reachable_states', 'white_tail_completed_pairs',
                                          'shared_tail_completed_pairs', 'literal_full_support_controls',
                                          'forward_first_Common_failure_time', 'forward_witness_followup')}, indent=2))


if __name__ == '__main__':
    main()
