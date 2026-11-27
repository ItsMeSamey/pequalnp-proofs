"""Full-cube positive controls for terminal decoding with four and five hot ANDs."""
def trace(mask, targets):
    clean = 6 - len(targets)
    hot = set()
    for axis, target in enumerate(targets, clean):
        if mask >> (2 * axis) & 3 == 3:
            hot.add(axis)
            mask |= target
    return any(mask >> (2 * axis) & 3 == 3 for axis in range(clean)), hot

def check(targets, receivers):
    all_hot = set()
    for state in range(1 << len(receivers)):
        mask = 0
        for i, raw in enumerate(receivers):
            if state >> i & 1:
                mask |= raw
        accepted, hot = trace(mask, targets)
        assert accepted == (state.bit_count() >= 2)
        if state.bit_count() == 1:
            all_hot.update(hot)
    assert len(all_hot) == len(targets)

check([5, 9, 6, 10], [3 << (2 * axis) for axis in range(2, 6)])
check([1, 1, 1, 2, 2], [sum(3 << (2 * i) for i in (1, 2, 3)),
                          sum(3 << (2 * i) for i in (4, 5))])
print("Four-hot and five-hot positive controls passed all 20 input states.")
