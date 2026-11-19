"""Literal truth-table check of a finite swap and its first failed lift."""

ORIGINAL = 2440786724530854946624415088918
AT_72 = 10500241303133006747930660018695972033202183908454678


def step(x):
    answer = 0
    for j in range(x.bit_length() + 1):
        a, b = (x >> (j + 1)) & 1, (x >> j) & 1
        c = (x >> (j - 1)) & 1 if j else 0
        answer |= ((30 >> (4 * a + 2 * b + c)) & 1) << j
    return answer


def history(x, steps):
    rows = [x]
    for _ in range(steps):
        rows.append(step(rows[-1]))
    return rows


if __name__ == "__main__":
    old = history(ORIGINAL, 116)
    new = history(AT_72, 116 - 72)
    assert ORIGINAL.bit_length() == 101
    zeros = [t for t, x in enumerate(old) if (x & 1) == 0]
    assert zeros[0] == 0 and zeros[-3:] == [100, 106, 116]
    assert all(b-a in (6, 10) for a, b in zip(zeros, zeros[1:]))
    assert [t for t in range(72, 117) if (old[t] ^ new[t-72]) & 1] == [106, 110]
    assert old[111] == new[111-72]
    j_max = AT_72.bit_length()
    for wall in (0, 1):
        a, b = 0, wall
        for j in range(j_max + 2):
            choices = [
                v for v in (0, 1)
                if ((30 >> (4*v + 2*b + a)) & 1) == ((AT_72 >> j) & 1)
            ]
            assert len(choices) == 1
            a, b = b, choices[0]
        # All remaining output bits are zero. The only next predecessor
        # bit for input pair (1,1) and output zero is another one.
        assert (a, b) == (1, 1)
        assert [v for v in (0, 1) if ((30 >> (4*v + 3)) & 1) == 0] == [1]
    print("Legal through 116. Wall edits at 106 and 110. Whole row equal at 111.")
    print("Altered row finite at 72; both possible predecessors at 71 have black tails.")
