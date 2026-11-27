from itertools import product


def check():
    weight_tests = 0
    for d in (1, 2, 3, 4):
        q = 1 << d
        rotations = [((a << 1) & (q-1)) | (a >> (d-1)) for a in range(q)]
        answers = [w for w in product((0, 1), repeat=q)
                   if all(w[a] == w[r] and w[a] != w[a ^ 1]
                          for a, r in enumerate(rotations))]
        parity = tuple(a.bit_count() % 2 for a in range(q))
        assert set(answers) == {parity, tuple(1-x for x in parity)}
        for monomial in range(q-1):
            costs = [sum(v for a, v in enumerate(w) if a & monomial == monomial)
                     for w in answers]
            assert costs[0] == costs[1]
            weight_tests += 1
    return weight_tests


if __name__ == '__main__':
    print(check(), 'monomial ties checked across four exhaustive table sizes')
