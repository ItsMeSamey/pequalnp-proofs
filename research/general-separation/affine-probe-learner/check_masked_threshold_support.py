"""Original-word support audit; forecasts use plain threshold syntax."""
from functools import lru_cache
from forecast_consistency_search import decide, threshold
from odd_masked_circuit import compile_source
from check_binary_fault_solver import Source, raw


def instance(r,phi):
    c = Source(r+3)
    def either(a,b):
        return c.nand(c.inv(a),c.inv(b))
    last,f = -2,-1
    for i in range(r):
        last = c.both(last,i+3)
    for x in range(1<<r):
        if phi >> x & 1:
            term = -2
            for i in range(r):
                term = c.both(term,i+3 if x >> (r-1-i) & 1 else c.inv(i+3))
            f = either(term,f)
    choice = either(c.both(c.inv(0),f),c.both(0,last))
    return c.finish(c.both(c.both(1,2),choice))


def decode(m,x):
    free,tail = divmod(x,1<<m)
    for i in range(m):
        group = (free >> (3*i)) & 7
        tail ^= ((group>>2) ^ ((group>>1) & group & 1)) << i
    return tail


def mids(w,p):
    a,b = -1,(1<<w)-1
    while b-a > 1:
        t = (a+b)//2
        yield t
        if t >= p:
            b = t
        else:
            a = t


def check(r,phi,driver):
    m = r+3
    w = 4*m
    F = instance(r,phi)
    G = compile_source(m,F)
    planted = (1<<m)-1
    assert raw(w,G,planted) and not raw(w,G,0)
    limit = 1 << (m-1)
    models = [x for x in range(limit+1) if raw(w,G,x)]
    assert models == [(3<<r)+v for v in range(1<<r) if phi >> v & 1]
    for x in range((1<<w) if r == 0 else (1<<m)):
        assert raw(w,G,x) == raw(m,F,decode(m,x))
    stages = []
    hi = (1<<w)-1
    for h in reversed(range(m-1,w)):
        p = 1<<h
        tests = list(mids(w,p))
        assert hi == 2*p-1 and p in tests and p-1 in tests
        assert not raw(w,G,p)
        if h >= m:
            assert planted <= p-1 and decode(m,p).bit_count() <= 1
        for j in tests:
            assert (2*min(hi,j)>hi) == (j >= p)
        stages.append((hi,p,tests))
        hi = p-1
    assert len(stages) == 3*m+1
    if not driver:
        return
    @lru_cache(None)
    def T(j):
        return threshold(w,j)
    seen = []
    class Done(Exception):
        pass
    def predict(n,cap,history,query):
        assert n == w and len(query[0]) <= cap
        if not history:
            assert query == G and not seen
            return 0
        i = len(history)-1
        assert history == ((G,1),)+tuple((T(p-1),1) for _,p,_ in stages[:i])
        if i == len(stages):
            raise Done
        hi,p,tests = stages[i]
        if len(seen) == i:
            seen.append([])
        j = tests[len(seen[-1])]
        assert query == T(j)
        seen[-1].append(j)
        return int(2*min(hi,j)>hi)
    try:
        decide(w,G,predict,'positive')
    except Done:
        pass
    else:
        raise AssertionError('missing target crossing')
    assert seen == [tests for _,_,tests in stages]


if __name__ == '__main__':
    for r in range(3):
        for phi in range(1 << (1<<r)):
            check(r,phi,r == 1 and phi in (0,3))
    print('Original masked supports and plain-threshold histories agree.')
