"""Finite open strips, with either bit allowed at each outside boundary per tick."""
import networkx as nx


def next_rows(width):
    mask = (1 << width) - 1
    return {
        row: sorted({
            (((row << 1) | west) ^ (row | (row >> 1) | (east << (width - 1)))) & mask
            for west in (0, 1) for east in (0, 1)
        }) for row in range(mask + 1)
    }


def graph(width):
    nxt = next_rows(width)
    mask = (1 << width) - 1
    g = nx.DiGraph()
    for a in nxt:
        for b in nxt[a]:
            for c in nxt[b]:
                for d in nxt[c]:
                    changed = (a ^ b) | (b ^ c) | (c ^ d)
                    if changed == mask:
                        g.add_edge((a, b, c), (b, c, d))
    return g


if __name__ == "__main__":
    for width in range(1, 9):
        g = graph(width)
        recurrent = [s for s in nx.strongly_connected_components(g)
                     if len(s) > 1 or any(g.has_edge(x, x) for x in s)]
        print(width, len(g), sorted((len(s) for s in recurrent), reverse=True)[:10],
              sum(g.subgraph(s).number_of_edges() > len(s) for s in recurrent))
