"""Compare every recurrent four-row window from two different enumerations."""
from extend import extend, graph, recurrent
from verify import recurrence_at_width

g = recurrent(graph(3))
for width in range(4, 20):
    g = extend(g, width - 1)
wins = {
    tuple(sum(((row >> i) & 1) << t for t, row in enumerate((*src, dst[2])))
          for i in range(19))
    for src, dst in g.edges
}
assert wins == recurrence_at_width()
print("Independent constructions agree on all 495 recurrent edges.")
