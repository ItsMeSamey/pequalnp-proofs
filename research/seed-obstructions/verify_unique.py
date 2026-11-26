"""Verify equality signatures by forced membership alone."""
from verify_mixed import coords, front, sets, target

def classify(axis, width, expected):
    data = [coords(k) for k in range(676)]
    constraints = sorted({
        (data[p][axis], data[n][axis])
        for p in range(676) if (target ^ front) >> p & 1
        for n in range(676) if not (target >> n & 1)
        if not data[p][1-axis] & ~data[n][1-axis]
    })
    assert all(a.bit_count() == 1 and not a & b for a, b in constraints)
    packed = sets[('point','line')[axis]]
    required = [data[p][axis] for p,n in packed]
    forbidden = [data[n][axis] for p,n in packed]
    while True:
        previous = required.copy(), forbidden.copy()
        for a,b in constraints:
            eligible = [i for i in range(7) if not (forbidden[i] & a or required[i] & b)]
            assert eligible
            if len(eligible) == 1:
                i = eligible[0]
                required[i] |= a
                forbidden[i] |= b
        if previous == (required, forbidden):
            break
    assert all(not a & b and a | b == 2**width-1 for a,b in zip(required, forbidden))
    assert sorted(required) == sorted(expected)
    print(('point','line')[axis], len(constraints), 'constraints force', required)

if __name__ == '__main__':
    classify(0,13,[sum(1<<((6+j+d)%13) for d in [0,1,3,9]) for j in range(7)])
    classify(1,7,[1<<j for j in range(7)])
