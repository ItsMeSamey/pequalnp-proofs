"""Original-coordinate range counts and witnesses for the bounded fixtures."""
from random import Random
from check_binary_fault_solver import Source, raw
from check_odd_masked_circuit import source
from check_masked_threshold_support import instance
from odd_masked_circuit import compile_source
from tail_permutation_range import recognize, solve


def intervals(analysis,prefix,tests):
    for a,b in tests:
        expected = prefix[b+1]-prefix[a] if a<=b else 0
        assert analysis.range_count(a,b) == expected
        word = analysis.witness(a,b)
        if expected:
            assert type(word) is int and a<=word<=b
            assert prefix[word+1]-prefix[word] == 1
        else:
            assert word is None


def small(h,F,tests=None,bound=None):
    obj = recognize(h,F)
    m = obj.m
    assert obj.h == h and obj.width == m and 0 <= m <= h
    if bound is not None:
        assert m <= bound
    size = 1<<h
    fibers = [0]*(1<<m)
    prefix = [0]
    for y in range(1<<m):
        assert obj.rank(y,-1) == 0
    for x in range(size):
        u,t = divmod(x,1<<m)
        y = obj.project(x)
        assert y == (t ^ obj.offset(u)) and obj.lift(u,y) == x
        truth = raw(h,F,x)
        assert truth == raw(m,obj.F,y)
        prefix.append(prefix[-1]+truth)
        fibers[y] += 1
        for z,count in enumerate(fibers):
            assert obj.rank(z,x) == count
    assert all(count == 1<<(h-m) for count in fibers)
    if tests is None:
        tests = ((a,b) for a in range(size) for b in range(size))
    intervals(obj,prefix,tests)
    intervals(obj,prefix,[(0,-1),(size,size-1)])


def seeded():
    rng = Random(94201)
    for h in range(4):
        for _ in range(5):
            gates = []
            for i in range(rng.randrange(9)):
                gates.append(tuple(rng.randrange(-2,h+i) for _ in range(2)))
            out = rng.randrange(-2,h+len(gates))
            small(h,(tuple(gates),out))
    c = Source(4)
    noise = c.both(0,1)
    left,right = c.xor(noise,2),c.xor(3,noise)
    small(4,c.finish(c.both(left,c.inv(right))))


def masks():
    for n in (0,1):
        for table in range(1 << (1<<n)):
            small(4*n,compile_source(n,source(n,table)),bound=n)
    F = compile_source(2,source(2,6))
    small(8,F,[(0,255),(0,0),(1,0),(7,8),(31,144),(253,255)],2)


def historical():
    for phi in (0,1):
        F = compile_source(3,instance(0,phi))
        obj = recognize(12,F)
        assert obj.m <= 3
        # Each bit is a distinct original assignment. Evaluate each raw gate
        # once in parallel without using recognition, the source decoder, or
        # the range evaluator; spot-check indexing against scalar NANDs.
        total = 1 << 12
        full = (1 << total)-1
        values = {-1:0,-2:full}
        for i in range(12):
            block = 1 << (11-i)
            pattern = ((1 << block)-1) << block
            values[i] = pattern * (full // ((1 << (2*block))-1))
        for w,(a,b) in enumerate(F[0],12):
            values[w] = full ^ (values[a] & values[b])
        vector = values[F[1]]
        for x in (0,1,3,4,7,8,255,1536,4095):
            assert ((vector >> x) & 1) == raw(12,F,x)
        prefix = [0]
        for x in range(total):
            prefix.append(prefix[-1]+((vector >> x)&1))
        hi = 4095
        tests = []
        for shift in reversed(range(3,12)):
            median = 1<<shift
            assert prefix[median+1] == prefix[median]
            tests.extend(((0,hi),(0,median),(median,median)))
            hi = min(hi,median-1)
        assert hi == 7 and prefix[8]-prefix[7] == 1
        tests.extend(((0,7),(0,4),(3,3),(4,4),(7,7)))
        intervals(obj,prefix,tests)
        assert obj.range_count(0,4) == phi
        assert obj.witness(0,4) == (3 if phi else None)


def public_api():
    for out in (-1,-2):
        obj = solve(0,((),out),0,0,max_latents=1)
        assert obj['count'] == int(out == -2) and obj['latent_width'] == 0
        assert obj['status'] == ('witness' if out == -2 else 'unsat')
        if out == -2:
            assert obj['assignment'] == 0
    # Direct MSB output bypasses every potential suffix cut.
    F = ((),0)
    obj = recognize(2,F)
    assert obj.m == 2 and obj.cuts == (0,1)
    assert solve(2,F,0,3,max_latents=3) == dict(status='unknown',
        reason='latent_budget',required=4,available=3,latent_width=2)
    full = solve(2,F,0,3,max_latents=4)
    assert full['count'] == 2 and full['assignment'] in (2,3)
    assert solve(2,F,0,-1,max_latents=0)['count'] == 0
    for lo,hi,budget in ((-1,2,4),(0,4,4),(0,2,-1),(0,-1,-1)):
        try:
            solve(2,F,lo,hi,max_latents=budget)
        except ValueError:
            continue
        raise AssertionError('invalid budget or endpoint accepted')


if __name__ == '__main__':
    for stage in (public_api,seeded,masks,historical):
        stage()
        print(f'{stage.__name__} passed',flush=True)
