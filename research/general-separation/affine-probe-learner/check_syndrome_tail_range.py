"""Original-word rank, lift and range-count checks for syndrome compression."""
from syndrome_tail_range import recognize, _candidate
from tail_permutation_range import recognize as permutation
from check_binary_fault_solver import Source


def values(n,F,x):
    v = {-1:0,-2:1}
    for i in range(n):
        v[i] = (x >> (n-1-i)) & 1
    for j,(a,b) in enumerate(F[0],n):
        v[j] = 1-(v[a]*v[b])
    return v


def audit(h,F,obj,all_intervals=False):
    bins = [[] for _ in range(1<<obj.m)]
    accepted = [0]
    for y in range(len(bins)):
        assert obj.rank(y,-1) == 0
    for x in range(1<<h):
        v = values(h,F,x)
        y = 0
        for cut in obj.cuts:
            y = 2*y+v[cut]
        assert y == obj.project(x)
        bins[y].append(x)
        assert v[F[1]] == values(obj.m,obj.F,y)[obj.F[1]]
        accepted.append(accepted[-1]+v[F[1]])
        for z,original in enumerate(bins):
            assert obj.rank(z,x) == len(original)
    for z,original in enumerate(bins):
        assert len(original) == 1<<(h-obj.m)
        assert all(obj.lift(i,z) == x for i,x in enumerate(original))
    size = 1<<h
    cases = [(0,-1),(size,size-1)]
    cases.extend((0,b) for b in range(size))
    if all_intervals:
        cases.extend((a,b) for a in range(size) for b in range(size))
    for a,b in cases:
        expected = accepted[b+1]-accepted[a] if a<=b else 0
        assert obj.range_count(a,b) == expected
        w = obj.witness(a,b)
        if expected:
            assert type(w) is int and a<=w<=b and accepted[w+1]>accepted[w]
        else:
            assert w is None


def growing():
    for h in (4,5,6,10):
        c = Source(h)
        a,b = 0,1
        for i in range(2,h):
            a = c.xor(a,i)
        for i in range(2,h):
            b = c.xor(b,i)
        F = c.finish(c.nand(a,b))
        assert permutation(h,F).m == h
        obj = recognize(h,F)
        assert obj.m == 2 and obj.tail_width >= obj.m
        if h<=5:
            audit(h,F,obj,all_intervals=(h==4))
        else:
            assert obj.range_count(0,(1<<h)-1) == 3*(1<<(h-2))


def dependencies():
    c = Source(5)
    noise = c.nand(0,1)
    # Slopes (100,010,110) with the same nonlinear prefix offset
    # on the first and third cuts, leaving one free physical suffix bit.
    u,v = c.xor(2,noise),3
    w = c.xor(c.xor(2,3),noise)
    F = c.finish(c.nand(c.nand(u,v),w))
    rect = _candidate(5,F,3)
    assert rect is not None and (rect.m,rect.tail_width) == (2,3)
    audit(5,F,rect)
    # Equal slopes with two uncancelled prefix tokens must be rejected.
    c = Source(3)
    a,b = c.xor(0,2),c.xor(1,2)
    F = c.finish(c.nand(a,b))
    assert _candidate(3,F,1) is None
    audit(3,F,recognize(3,F),True)
    for h in (0,2):
        for bit in (-1,-2):
            F = ((),bit)
            obj = recognize(h,F)
            assert obj.m == 0
            audit(h,F,obj,True)


if __name__ == '__main__':
    dependencies()
    print('Dependent offsets, rectangular and empty ranks passed.',flush=True)
    growing()
    print('Overlapping parity chains and original prefixes passed.',flush=True)
