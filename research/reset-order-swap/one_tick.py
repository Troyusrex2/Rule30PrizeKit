"""Independent 64-case check for one backward tick at every legal phase."""
from itertools import product
from physical_check import seed


def advance(register, output):
    shallow, current = register
    deeper, = [bit for bit in (0, 1)
               if ((30 >> (4*bit + 2*current + shallow)) & 1) == output]
    return current, deeper


def check(gaps, phase):
    stops = (0, gaps[0], gaps[0]+gaps[1], sum(gaps))
    n = sum(gaps) + 1 - phase
    word = sum((t not in stops) << (t-phase) for t in range(phase, sum(gaps)+1))
    initial = seed(n, word)
    left, right = (0, 0), (0, 1)
    for j in range(n):
        bit = (initial >> j) & 1
        left, right = advance(left, bit), advance(right, bit)
        if left == right:
            return j+1
    raise AssertionError((gaps, phase))


if __name__ == "__main__":
    depths = [check((d, a, b), phase) for d, a, b in product((6,10), repeat=3)
              for phase in range(d)]
    assert len(depths) == 64 and max(depths) == 11
    print("64 phases/continuations checked; both predecessor registers agree by depth 11.")
