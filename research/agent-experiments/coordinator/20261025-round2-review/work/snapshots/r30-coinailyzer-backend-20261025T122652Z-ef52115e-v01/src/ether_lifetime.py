"""F002 support: lifetime of the truncated period-seven row in the 0101 guard.
For width l, report the first even time at which depth 1 is white (InX fails)
and the number of double steps j for which next^j(row) still passes the
13-double-step guard with the alternating stream (Safe13-style)."""
import json
from zbl import ether, next2, col1
out = []
for l in [30, 40, 60, 100, 160, 240]:
    c = col1(ether(l), 2 * l + 40)
    fail = next(t for t in range(0, len(c), 2) if c[t] == 0)
    w = ether(l); j = 0
    while True:
        cc = col1(w, 27)
        st = [0, 1] * 7 if j % 2 == 0 else [1, 0] * 7
        if not (all(cc[2 * i] == 1 for i in range(14)) and all(cc[2 * i + 1] == st[i] for i in range(13))):
            break
        j += 1; w = next2(w)
    out.append({"width": l, "first_white_even_time": fail, "double_steps_in_guard": j, "positive_defect_steps": (j + 1) // 2})
print(json.dumps(out, indent=1))
