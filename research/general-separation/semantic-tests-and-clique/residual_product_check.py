from itertools import product


def residuals(table, size, live_mask):
    live = [i for i in range(size) if live_mask >> i & 1]
    fixed = [i for i in range(size) if not live_mask >> i & 1]
    values = set()
    for pins in product(range(2), repeat=len(fixed)):
        fixed_input = sum(bit << pos for pos, bit in zip(fixed, pins))
        residual = []
        for bits in product(range(2), repeat=len(live)):
            value = fixed_input + sum(bit << pos for pos, bit in zip(live, bits))
            residual.append(table >> value & 1)
        values.add(tuple(residual))
    return values


def positive_count(values):
    return sum(any(row) for row in values)


def sign_count(values):
    return len({tuple(x ^ row[0] for x in row) for row in values})


for gate in ('and', 'xor'):
    tested = 0
    for left, right in product(range(1, 16), repeat=2):
        entries = [(left >> (x & 3) & 1, right >> (x >> 2) & 1)
                   for x in range(16)]
        table = sum((a & b if gate == 'and' else a ^ b) << x
                    for x, (a, b) in enumerate(entries))
        count = positive_count if gate == 'and' else sign_count
        for mask in range(16):
            left_count = count(residuals(left, 2, mask & 3))
            right_count = count(residuals(right, 2, mask >> 2))
            assert count(residuals(table, 4, mask)) == left_count * right_count
            tested += 1
    print(gate, tested)
