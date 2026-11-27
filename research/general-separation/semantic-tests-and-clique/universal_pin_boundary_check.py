"""Exhaustive raw minors on a fixed 17-vertex graph with three named pins."""
from itertools import product
from mixed_principal_channels_check import channel_keys, enumerate_states, minor, span_test


def host():
    rows = [0] * 17
    for v in range(1, 8):
        a = 2*v + 1
        b = a + 1
        rows[a] = v | (1 << b)
        rows[b] = 1 << a
        for pin in range(3):
            rows[pin] |= ((v >> pin) & 1) << a
    return rows


def main():
    keys = list(channel_keys())
    states = {}
    principal_masks = set()
    assignments = 0
    for modes in product(range(3), repeat=7):
        rows = host()
        for v, mode in enumerate(modes, 1):
            a = 2*v + 1
            b = a + 1
            rows[a] |= int(mode == 2) << a
            rows[b] |= int(mode >= 1) << b
        values = [minor(rows, left, right) for left, right in keys]
        channel = sum(bit << i for i, bit in enumerate(values))
        principal = sum(bit << sum(1 << i for i in left)
                        for bit, (left, right) in zip(values, keys) if left == right)
        principal_masks.add(principal)
        bits = []
        for d in range(8):
            toggled = rows[:]
            for i in range(3):
                toggled[i] ^= d & (1 << i)
            bits.append(minor(toggled))
        isolates = [j for j, bit in enumerate(bits) if bit and all(
            not bits[j ^ step] for step in (1, 2, 4))]
        labels = 0 in isolates, bool(isolates)
        assert states.setdefault(channel, labels) == labels
        assignments += 1
    assert states == enumerate_states()
    for parity in (0, 1):
        slots = [i for i in range(8) if i.bit_count() % 2 == parity]
        patterns = {sum((m >> j & 1) << i for j, i in enumerate(slots)) for m in range(1, 16)}
        assert patterns <= principal_masks
    print(assignments, "assignments;", len(states), "mixed states;", len(principal_masks),
          "principal masks; all 15 pure patterns per parity")
    for mode in range(2):
        print(["fixed", "fiber"][mode], [span_test(states, mode, d) for d in (1, 2, 3)])


if __name__ == "__main__":
    main()
