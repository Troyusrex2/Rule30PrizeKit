"""Exact spatial cycle certificates for prescribed periodic wall traces.

Python 3.10+. The integer column stores time phase t in bit t.
"""
from itertools import accumulate


def initial_columns(gaps):
    period = sum(gaps)
    reset_phases = list(accumulate((0, *gaps[:-1])))
    mask = (1 << period) - 1
    center = mask
    for phase in reset_phases:
        center ^= 1 << phase
    return period, reset_phases, 0, center


def spatial_step(shallow, current, period):
    shifted = (current >> 1) | ((current & 1) << (period - 1))
    return current, shifted ^ (shallow | current)


def orbit(gaps, cap=20000):
    period, phases, a, b = initial_columns(gaps)
    first, columns = {}, []
    for depth in range(cap + 1):
        if (a, b) in first:
            onset = first[a, b]
            return columns, onset, depth-onset, phases
        first[a, b] = depth
        columns.append(b)
        a, b = spatial_step(a, b, period)
    raise ValueError('no certified repeat within cap')


def sharp_slack(columns, onset, length, phase):
    def black(j):
        if j >= onset:
            j = onset + (j-onset) % length
        return (columns[j] >> phase) & 1

    assert any(black(j) for j in range(onset, onset+length))
    longest, witness = 0, 0
    for width in range(onset + length):
        gap = 0
        while not black(width+gap):
            gap += 1
        if gap > longest:
            longest, witness = gap, width
    return longest, witness


def literal_check(columns, onset, length, gaps, phases):
    # Verify every full temporal column transition, including cycle wrap,
    # by the original local truth table without rotations or bitwise OR.
    period = sum(gaps)
    def col(j):
        if j == -1:
            return 0
        return columns[j if j < onset else onset + (j-onset) % length]

    for j in range(onset+length+1):
        for t in range(period):
            neighbors = [((col(i) >> t) & 1) for i in (j+1,j,j-1)]
            index = 4*neighbors[0] + 2*neighbors[1] + neighbors[2]
            assert (30 >> index) & 1 == (col(j) >> ((t+1) % period)) & 1
    # For small widths compare the exact predicted first mismatch with
    # direct forward simulation of the maximizing finite row.
    for phase in phases:
        for width in range(31):
            seed = sum(((col(j) >> phase) & 1) << j for j in range(width))
            first = width
            while not ((col(first) >> phase) & 1):
                first += 1
            x = seed
            for t in range(first+1):
                target = (col(0) >> ((phase+t) % period)) & 1
                assert ((x & 1) != target) == (t==first)
                x = (x >> 1) ^ (x | (x << 1))


if __name__ == '__main__':
    for gaps in [(6,), (10,), (6,10), (6,6,10), (6,10,10)]:
        columns, onset, length, phases = orbit(gaps)
        literal_check(columns,onset,length,gaps,phases)
        answers = [sharp_slack(columns,onset,length,p) for p in phases]
        print(gaps, 'spatial pair orbit', (onset,length),
              'max excess and attaining width by reset phase', list(zip(phases,answers)))
