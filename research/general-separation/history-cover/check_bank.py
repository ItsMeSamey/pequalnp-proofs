import random
from bank import compress
from cover import conflicts, direct, search_cover
from check import exhaustive_backend


def example(k):
    n = 4*k
    raw = lambda j: 1 << (j+1)
    z = lambda j: 1 << (n+1+j)
    gates = [(raw(2*j),raw(2*j+1),0) for j in range(2*k)]
    halves = [sum(z(i) for i in range(l,l+k)) for l in (0,k)]
    for h in range(n*(n-1).bit_length()-len(gates)):
        prev = z(len(gates)-1) if h else raw(0)
        gates.append((prev^raw((h+1)%n),halves[h%2]^raw(h%n),raw((h+2)%n)))
    return n,gates,z(len(gates)-1)


def main():
    rng = random.Random(876)
    for k in [1,2,4,6]:
        n,g,out=example(k)
        sys,stats=compress(n,g,out,0)
        assert stats['banks']==[(2*k,2,4*k)]
        edges=conflicts(n,g,out)
        assert all((i,j) in edges for i in range(k) for j in range(k,2*k))
        assert search_cover(edges,k-1) is None
        inputs=range(1<<n) if n<=8 else [rng.randrange(1<<n) for _ in range(150)]
        assert all(sys.evaluate(x)==direct(n,g,out,x) for x in inputs)
        print(k,n,len(g),stats)
    for case in range(250):
        n,m=rng.randint(1,4),rng.randint(1,6)
        g=[tuple(rng.randrange(1<<(n+i+1)) for _ in range(3)) for i in range(m)]
        out=rng.randrange(1<<(n+m+1))
        for stages in [0,1,2,m]:
            sys,stats=compress(n,g,out,m,stages)
            assert all(sys.evaluate(x)==direct(n,g,out,x) for x in range(1<<n))
            if case < 25 and len(sys.definitions)<=4:
                assert sys.count_witness(exhaustive_backend)[0]==sys.count_witness()[0]
    # Gate 1 depends on gate 0. Its equation cannot be dropped as raw-only.
    n=3
    g=[(2,4,0),(16,8,0)]
    for stages, expected in [(1,[1]),(2,[1,1])]:
        sys,stats=compress(n,g,32,0,stages)
        assert [x[0] for x in stats['banks']]==expected
        assert sys.count_witness()==(1,7)
    print('250 random circuits, four stage budgets; mixed dependency control passed')


if __name__=='__main__':
    main()
