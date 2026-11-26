"""Extend recurrent open strips by overlap; exact for recurrent edges at width >=3."""
from collections import defaultdict

import networkx as nx

from strip import graph


def recurrent(g):
    out = nx.DiGraph()
    for s in nx.strongly_connected_components(g):
        if len(s) > 1 or any(g.has_edge(x, x) for x in s):
            out.add_edges_from(g.subgraph(s).edges())
    return out


def extend(g, w):
    # Two width-w constraints cover all interior update neighborhoods of width w+1.
    # The western and eastern outer neighbors are independent at each tick.
    mask = (1 << (w - 1)) - 1
    by_low = defaultdict(list)
    windows = [(*u, v[2]) for u, v in g.edges()]
    for win in windows:
        by_low[tuple(x & mask for x in win)].append(win)
    grown = nx.DiGraph()
    for low in windows:
        for high in by_low[tuple(x >> 1 for x in low)]:
            joined = tuple(x | (y << 1) for x, y in zip(low, high))
            grown.add_edge(joined[:3], joined[1:])
    return recurrent(grown)


if __name__ == "__main__":
    g = recurrent(graph(3))
    for w in range(4, 33):
        g = extend(g, w - 1)
        if w <= 8:
            assert set(g.edges) == set(recurrent(graph(w)).edges)
        print(w, len(g), g.number_of_edges(), len(list(nx.strongly_connected_components(g))))
