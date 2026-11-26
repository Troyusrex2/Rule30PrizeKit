"""The kit's physical period-15 trap and all western depths, including its cycle."""
from itertools import groupby


def main():
    p, gate = 15, 18864  # trap001fifteen.u; state x0 at label 0 is finite on the right.
    mask = (1 << p) - 1
    def advance(col, k):
        return ((col >> k) | (col << (p - k))) & mask

    center = sum(1 << k for k in range(2, p, 3))
    # At the black phases the actual right neighbor is masked in the first inversion.
    east = gate & ~center
    seen, no_four = {}, []
    while (center, east) not in seen:
        seen[center, east] = len(no_four)
        future = [advance(center, k) for k in range(4)]
        changed = (future[0] ^ future[1]) | (future[1] ^ future[2]) | (future[2] ^ future[3])
        no_four.append(changed == mask)
        center, east = future[1] ^ (center | east), center
    onset = seen[center, east]
    cycle = no_four[onset:]
    assert not all(cycle)
    # Two copies test runs crossing the join as well as those in the transient.
    length = max(len(list(g)) for b, g in groupby(no_four + cycle) if b)
    assert (onset, len(cycle), length) == (83, 2145, 6)
    assert no_four[2] and not no_four[6]
    print("Western spatial transient 83, cycle 2145; longest four-free band 6.")


if __name__ == "__main__":
    main()
