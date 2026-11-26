from random import Random
from solver import affine_count, bits, count_outside, parity, solve


def brute(rank, labels, ordinary, t, target, root_label, moments, tests, s):
    # Enumerate covectors and, for each, enumerate ordinary subsets by reachable XOR sums.
    for d in range(1<<rank):
        if parity(t&d) or (s is not None and not parity(s&d)) or any(parity(m&d)!=b for m,b in tests):
            continue
        sums={0}
        for v,l in ordinary:
            if not parity(v&d):
                a=v|(l<<rank)
                sums |= {x^a for x in sums}
        req=target^root_label
        for i,m in enumerate(moments):
            req ^= parity(m&d)<<i
        if t|(req<<rank) in sums:
            return True
    return False


def check(rank, labels, ordinary, fillers, t, target, root_label, moments, tests, s):
    result=solve(rank,labels,ordinary,fillers,t,target,root_label,moments,tests,s)
    expected=brute(rank,labels,ordinary,t,target,root_label,moments,tests,s)
    assert (result is not None)==expected
    if result is not None:
        d,mask=result
        assert not parity(d&t) and (s is None or parity(d&s))
        assert all(parity(d&m)==b for m,b in tests)
        vx=0
        lx=target^root_label
        for i in bits(mask):
            v,l=ordinary[i]
            assert not parity(v&d)
            vx ^= v
            lx ^= l
        assert vx==t and lx==sum(parity(m&d)<<j for j,m in enumerate(moments))


if __name__=='__main__':
    rng=Random(63138)
    exact=0
    for sub in range(1<<8):
        cols=[(v&3,v>>2) for v in range(8) if (sub>>v)&1]
        for t in range(4):
            for b in (0,1):
                check(2,1,cols,[],t,b,0,[2],[],1)
                exact+=1
    for _ in range(900):
        rank=rng.randrange(6)
        p=rng.randrange(4)
        n=rank+p
        base=[rng.getrandbits(n) for _ in range(rng.randrange(5))]
        # Basis elements plus all pair sums span every functional kernel,
        # including in the presence of zero columns or redundant generators.
        f=base+[v^w for i,v in enumerate(base) for w in base[:i]]
        allv=f+[rng.getrandbits(n) for _ in range(rng.randrange(7))]
        cols=[(a% (1<<rank),a>>rank) for a in allv]
        tests=[(rng.getrandbits(rank),rng.randrange(2)) for _ in range(rng.randrange(4))]
        check(rank,p,cols,range(len(f)),rng.getrandbits(rank),rng.getrandbits(p),
              rng.getrandbits(p),[rng.getrandbits(rank) for _ in range(p)],tests,
              rng.choice([None,rng.getrandbits(rank)]))
    for _ in range(400):
        rank=rng.randrange(7)
        def eqs():
            return [(rng.getrandbits(rank),rng.randrange(2)) for j in range(rng.randrange(5))]
        tests=eqs()
        bad=[eqs() for j in range(rng.randrange(5))]
        def ok(d,T):
            return all(parity(d&m)==b for m,b in T)
        assert affine_count(rank,tests)==sum(ok(d,tests) for d in range(1<<rank))
        assert count_outside(rank,tests,bad)==sum(ok(d,tests) and not any(ok(d,T) for T in bad) for d in range(1<<rank))
    # High filler rank with a certified small quotient: avoids exponential dual enumeration.
    rank=60
    base=[1<<j for j in range(rank-1)]
    f=base+[v^w for i,v in enumerate(base) for w in base[:i]]
    cols=[(v,0) for v in f]+[(1<<(rank-1),1)]
    d,I=solve(rank,1,cols,range(len(f)),(1<<(rank-1))|4,target=1,s=2)
    assert d&2 and not parity(d&((1<<(rank-1))|4))
    vx=0
    for i in bits(I):
        vx ^= cols[i][0]|(cols[i][1]<<rank)
    assert vx==(1<<rank)|(1<<(rank-1))|4
    print(f"Passed {exact} exhaustive instances, 900 promised instances, 400 counts, and a rank-60 witness.")
