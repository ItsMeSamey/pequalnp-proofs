"""Raw-word controls for affine tap separator model counting."""
from random import Random
from linear_tap_separator import solve, padded_path_source


def raw(n,F,x):
    values = {-1:0,-2:1,**{i:(x>>(n-1-i))&1 for i in range(n)}}
    for w,(a,b) in enumerate(F[0],n):
        values[w] = 1-values[a]*values[b]
    return values[F[1]]


def brute(n,F,merges=None):
    words = {x for x in range(1<<n) if raw(n,F,x)}
    result = solve(n,F,merges=merges)
    assert result['count'] == len(words)
    assert result['status'] == ('witness' if words else 'unsat')
    if words:
        assert result['assignment'] in words
    else:
        assert result['assignment'] is None
    return result


def schedules():
    # Three live NANDs plus the output factor. First selected merge crosses
    # time order, and another groups the output pin before its producer.
    F = (((0,1),(1,2),(3,4)),5)
    for merges in (None,((0,2),(3,1),(5,4)),((3,0),(4,2),(1,5))):
        result = brute(3,F,merges)
        assert result['factors'] == 4
        needed = 1 << result['separator_width']
        assert solve(3,F,merges=merges,max_states=needed) == result
        assert solve(3,F,merges=merges,max_states=needed-1) == {
            'status':'unknown','reason':'separator_budget','required':needed,'available':needed-1}
    for invalid in ([(0,0)],[(0,2),(0,1)],[(1,2)]):
        try:
            solve(3,F,merges=invalid)
        except ValueError:
            continue
        raise AssertionError('invalid schedule accepted')
    # Dead original nonlinear gates precede and follow a live one, creating
    # gaps in allocated coordinate labels. The fourth raw bit remains free.
    dead = (((1,2),(0,1),(2,3)),5)
    got = brute(4,dead)
    assert got['factors'] == 2 and got['count'] == 12
    assert brute(4,(dead[0],0))['factors'] == 1


def original_cases():
    for out in (-1,-2):
        brute(0,((),out))
    rng = Random(93206)
    for n in range(1,6):
        for _ in range(12):
            gates = []
            for i in range(rng.randrange(8)):
                gates.append(tuple(rng.randrange(-2,n+i) for _ in range(2)))
            out = rng.randrange(-2,n+len(gates))
            brute(n,(tuple(gates),out))


def path():
    for n,p in ((6,0),(6,2),(12,3),(18,11)):
        h,F = padded_path_source(n,p)
        assert h == n+p and len(F[0]) == 4*(h-1)+4*n+3*(n-1)
        a,b = 0,1
        for _ in range(n+2):
            a,b = b,a+b
        got = solve(h,F,max_states=512)
        assert got['status'] == 'witness' and got['separator_width'] <= 9
        assert got['global_rank'] >= n
        assert got['count'] == a*(1<<p)
        assert raw(h,F,got['assignment']) == 1
        if n==6:
            counts = [0]*(1<<p)
            for x in range(1<<h):
                parity = x.bit_count()%2
                taps = [parity ^ ((x>>(h-1-i))&1) for i in range(n)]
                expected = int(all(not (u and v) for u,v in zip(taps,taps[1:])))
                assert raw(h,F,x) == expected
                counts[x % (1<<p)] += expected
            assert counts == [a]*(1<<p)


if __name__=='__main__':
    for test in (schedules,original_cases,path):
        test()
        print(f'{test.__name__} passed',flush=True)
