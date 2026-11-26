"""Direct attempt to force a Jen contradiction on just columns -6 through -2."""
import networkx as nx

from strip import next_rows


def graph():
    nxt = next_rows(5)
    g = nx.DiGraph()
    for a in nxt:
        for b in nxt[a]:
            for c in nxt[b]:
                for d in nxt[c]:
                    for e in nxt[d]:
                        rows = a, b, c, d, e
                        west = tuple(x & 1 for x in rows)
                        east = tuple(x >> 4 for x in rows)
                        if west == (1, 0, 1, 0, 1):
                            continue
                        if len(set(east[:4])) == 1 or len(set(east[1:])) == 1:
                            continue
                        g.add_edge(rows[:4], rows[1:])
    return g


def witness(g):
    s = max(nx.strongly_connected_components(g), key=len)
    h = g.subgraph(s)
    home = min(s)
    outgoing = nx.single_source_shortest_path(h, home)
    returning = nx.single_source_shortest_path(h.reverse(), home)
    walks = []
    for target in sorted(s, key=lambda t: (len(outgoing[t]) + len(returning[t]), t)):
        path = outgoing[target] + list(reversed(returning[target]))[1:]
        seq = [v[-1] for v in path[1:]]
        for old in walks:
            first, second = old + seq, seq + old
            if all(any((x ^ y) & (1 << i) for x, y in zip(first, second)) for i in range(5)):
                return home, old, seq
        walks.append(seq)
    raise AssertionError("no witness")


if __name__ == "__main__":
    g = graph()
    state, a, b = witness(g)
    for seq in (a+b, b+a):
        v = state
        for x in seq:
            w = (*v[1:], x)
            assert g.has_edge(v, w)
            v = w
        assert v == state
    print("Initial history:", state, "loops:", a, b)
    print("Each site distinguishes AB from BA in an equal-length return.")
