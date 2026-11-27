"""Direct original-block checks and exact integer admissibility at three states."""
from check_binary_fault_solver import Source, raw
from forecast_consistency_search import threshold
from odd_masked_circuit import compile_source


def circuit(r,phi):
    g = b = r+2
    m = 1+g+r+b
    c = Source(m)
    guard = -2
    for i in range(g):
        guard = c.both(guard,1+i)
    last = -2
    for i in range(1+g,m):
        last = c.both(last,i)
    if r == 0:
        f = -2 if phi else -1
    else:
        x = 1+g
        f = (-1,c.inv(x),x,-2)[phi]
    left = c.both(c.inv(0),f)
    right = c.both(0,last)
    out = c.both(guard,c.nand(c.inv(left),c.inv(right)))
    return m,c.finish(out)


def shifted(prefix,m):
    value = 0
    for i in range(m):
        triple = (prefix >> (3*i)) & 7
        value |= ((triple>>2) ^ ((triple&3)==3)) << i
    return value


def admissible(counts,m):
    total = sum(counts)
    assert total > 0
    return tuple(i for i,k in enumerate(counts) if (k**4 << m) >= total**4)


def check(r,phi):
    m,F = circuit(r,phi)
    h,limit = 4*m,1<<m
    G = compile_source(m,F)
    w = limit-1
    U,T = threshold(h,w),threshold(h,limit//2)
    source_bits = []
    for s in range(limit):
        selector = s >> (m-1)
        guards = (s >> (2*r+2)) & ((1<<(r+2))-1)
        x = (s >> (r+2)) & ((1<<r)-1)
        low = s & ((1<<(r+2))-1)
        expected = (guards == (1<<(r+2))-1 and
                    ((not selector and (phi>>x)&1) or
                     (selector and x==(1<<r)-1 and low==(1<<(r+2))-1)))
        assert raw(m,F,s) == expected
        source_bits.append(int(expected))
    models = sum(source_bits)
    assert models == (phi.bit_count() << (r+2))+1

    # Each complete prefix has the same count: its tail images are precisely
    # one XOR translate. Independently evaluate full raw blocks, including
    # prefixes with correlated triple bits and the maximal original prefix.
    top = (1<<(3*m))-1
    blocks = {0,1,3,4,7,top,top//3}
    final = [0,0]
    for prefix in blocks:
        count = 0
        offset = shifted(prefix,m)
        for tail in range(limit):
            word = (prefix<<m)|tail
            bit = raw(h,G,word)
            assert bit == source_bits[tail^offset]
            count += bit
            if prefix == 0 and bit:
                final[raw(h,T,word)] += 1
        assert count == models
        for tail in (0,limit//2,w):
            word = (prefix<<m)|tail
            assert raw(h,U,word) == (word<=w)
            assert raw(h,T,word) == (word<=limit//2)

    whole_models = models << (3*m)
    counts = (((1<<h)-whole_models,whole_models),
              (whole_models-models,models),tuple(final))
    assert tuple(final) == (1,phi.bit_count() << (r+2))
    assert [admissible(pair,m) for pair in counts] == [(0,),(0,),(int(bool(phi)),)]
    assert (raw(h,G,w),raw(h,U,w),raw(h,T,w)) == (1,1,0)
    assert raw(h,G,limit//2) == 0


if __name__ == '__main__':
    for r in (0,1):
        for phi in range(1<<(1<<r)):
            check(r,phi)
        print(f'All {r}-input source tables passed.',flush=True)
