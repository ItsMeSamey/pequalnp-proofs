from itertools import product


def charts(m):
    n = 3*m
    swap = list(range(n))
    for i in range(m-1):
        a,b = 3*i+2, 3*i+3
        swap[a],swap[b] = b,a
    def rotated(a,power):
        return a//3*3+(a%3+power)%3
    for chart in product(range(2), repeat=m):
        F = [swap[rotated(a,1+chart[a//3])] for a in range(n)]
        R = [rotated(a,1-2*chart[a//3]) for a in range(n)]
        seen = set()
        u=0
        while u not in seen:
            seen.add(u)
            u=F[u]
        assert len(seen)==n
        for j in range(m):
            r = [int(a//3>j or (a//3==j and a%3==2)) for a in range(n)]
            W=[0]*n
            for i in range(m):
                a=3*i
                for _ in range(2):
                    u=R[a]
                    W[u]=W[a]^r[u]^r[F[u]]
                    a=u
            B=[x^y for x,y in zip(r,W)]
            assert r[0]^r[-1]
            for a in range(n):
                assert (B[a]^r[a]^W[a])==0
                assert (B[R[a]]^r[F[R[a]]]^W[a])==0
                if a//3!=j:
                    assert B[a]==B[R[a]] and W[a]==W[R[a]]
            yield 1


if __name__=='__main__':
    print(sum(sum(charts(m)) for m in range(1,10)), 'gate cocycles verified in 1022 compatible charts')
