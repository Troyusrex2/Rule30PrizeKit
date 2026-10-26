"""Complete finite-state input/output Subset relation under global Common.

One spatial graph, no width or temporal-horizon cutoff. Finite support is
closed by two white input symbols; all later outputs are identically white.
"""
from collections import deque
from pathlib import Path
import hashlib
import json

SOURCE = Path('D:/MWB/Rule30/agent-inbox/r30-codex-cedar-followup-20261026T154236Z-b768c9a6-v02/clock-review/published/work/dependencies/Rule30CommonPastResearch.lean')
SOURCE_SHA = '17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3'


def bits(s):
    return s & 1, (s >> 1) & 1, (s >> 2) & 1


def symbol(a, b, h):
    return a | (b << 1) | (h << 2)


def out_symbol(old2, old1, current):
    a0, b0, h0 = bits(old2)
    a1, b1, h1 = bits(old1)
    a, b, h = bits(current)
    return symbol(a ^ (a1 | a0), b ^ (b1 | b0),
                  h ^ ((1 ^ b0) & h1) ^ ((1 ^ a1) & h0))


def common(left, right):
    a, b, h = bits(left)
    aa, bb, hh = bits(right)
    return ((a ^ b) & hh) == (h & (aa ^ bb))


def bad(s):
    a, b, h = bits(s)
    return bool(h and not (a ^ b))


def advance(state, current):
    old2, old1, prevout, badin, badout = state
    output = out_symbol(old2, old1, current)
    reasons = []
    if not common(old1, current):
        reasons.append('input_Common')
    if not common(prevout, output):
        reasons.append('output_Common')
    if reasons:
        return None, output, reasons
    return (old1, current, output, badin or bad(current), badout or bad(output)), output, []


def flush(state):
    outputs = []
    for _ in range(2):
        state, output, reasons = advance(state, 0)
        outputs.append(output)
        if state is None:
            return {'valid': False, 'outputs': outputs, 'reasons': reasons}
    assert state[0] == state[1] == 0
    # A third white yields white output, so every later Common/Subset check
    # is automatic. This is a support argument, not a temporal cutoff.
    assert out_symbol(0, 0, 0) == 0 and common(state[2], 0)
    return {'valid': True, 'outputs': outputs,
            'input_Subset': not state[3], 'output_Subset': not state[4]}


def reconstruct(index, parents):
    result = []
    while parents[index] is not None:
        previous, s = parents[index]
        result.append(s)
        index = previous
    return result[::-1]


def main():
    root = Path(__file__).resolve().parent
    for marker in ('STOP', 'STOP_RESEARCH'):
        if (root.parents[1] / marker).exists():
            raise SystemExit('Session stop flag: ' + marker)
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA
    start = (0, 0, 0, False, False)
    states = [start]
    indexes = {start: 0}
    parents = [None]
    queue = deque([0])
    nodes = []
    witnesses = {}
    while queue:
        index = queue.popleft()
        state = states[index]
        completion = flush(state)
        if completion['valid']:
            key = str(int(completion['input_Subset'])) + str(int(completion['output_Subset']))
            if key not in witnesses:
                word = reconstruct(index, parents)
                witnesses[key] = {'input_symbols': word, 'length': len(word),
                                  'end_state': index, 'flush': completion}
        edges = []
        for s in range(8):
            target, output, reasons = advance(state, s)
            if target is None:
                edges.append({'input': s, 'output': output, 'target': None, 'reject': reasons})
                continue
            if target not in indexes:
                indexes[target] = len(states)
                states.append(target)
                parents.append((index, s))
                queue.append(indexes[target])
                assert len(states) <= 2048
            edges.append({'input': s, 'output': output, 'target': indexes[target]})
        assert len(nodes) == index
        nodes.append({'id': index, 'state': list(state), 'flush': completion, 'edges': edges})
    result = {
        'status': 'Complete finite-state closure; certificate needs independent audit',
        'source': str(SOURCE), 'source_sha256': SOURCE_SHA,
        'alphabet': 's=a+2*b+4*h; older to newer',
        'state': ['second_previous_input', 'previous_input', 'previous_output', 'input_bad_Subset_seen', 'output_bad_Subset_seen'],
        'initial_state': 0, 'state_upper_bound': 2048,
        'reachable_states': len(nodes), 'edges_checked': 8 * len(nodes),
        'graph_closed': True, 'nodes': nodes,
        'completed_Subset_pairs': sorted(witnesses), 'pair_order': 'input_Subset,output_Subset',
        'witnesses': witnesses,
        'backward_implication_holds': '01' not in witnesses,
        'forward_implication_holds': '10' not in witnesses,
        'boundary': 'two missing older white symbols; two explicit newer white symbols flush the entire finite output tail',
        'temporal_steps': 1, 'width_cutoff': None, 'search_horizon': None,
        'kernel_checked': False,
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (root / 'certificate.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: result[k] for k in ('status', 'reachable_states', 'edges_checked',
                                          'completed_Subset_pairs', 'witnesses',
                                          'backward_implication_holds', 'forward_implication_holds')}, indent=2))


if __name__ == '__main__':
    main()
