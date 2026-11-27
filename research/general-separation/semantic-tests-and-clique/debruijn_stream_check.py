"""Exhaust all maximum-period taps through width eight."""
from collections import Counter


def successor(state, taps, size):
    return ((state << 1) % size) | ((state & taps).bit_count() % 2)


def recurrence_possible(bits, degree):
    # Low degree bits are coefficients; bit degree is the RHS.
    basis = {}
    for pos in range(degree, len(bits)):
        row = (bits[pos] << degree) | sum(
            bits[pos - i - 1] << i for i in range(degree)
        )
        while row % (1 << degree):
            pivot = (row & -row).bit_length() - 1
            if pivot not in basis:
                basis[pivot] = row
                break
            row ^= basis[pivot]
        else:
            if row:
                return False
    return True


def check():
    counts = []
    for n in range(2, 9):
        size = 1 << n
        count = 0
        for taps in range(size // 2, size):
            state = 1
            orbit = []
            while not orbit or state != 1:
                orbit.append(state)
                state = successor(state, taps, size)
            if len(orbit) != size - 1:
                continue
            count += 1
            states = [0] + orbit
            bits = [state >> (n - 1) for state in states]
            twice = bits + bits
            assert len({tuple(twice[i:i+n]) for i in range(size)}) == size
            for k in range(n):
                frequencies = Counter(tuple(twice[i:i+k+1]) for i in range(size))
                assert len(frequencies) == 1 << (k + 1)
                assert set(frequencies.values()) == {size >> (k + 1)}
            overrides = 0
            for i, state in enumerate(states * 2):
                nxt = successor(state, taps, size)
                desired = states[(i + 1) % size]
                assert (nxt ^ int(state in (0, size // 2))) == desired
                overrides += nxt != desired
            assert overrides == 4
            assert not recurrence_possible(twice, size // 2)
        counts.append(count)
    print("maximum-period masks by width 2..8:", counts, "total:", sum(counts))


if __name__ == "__main__":
    check()
