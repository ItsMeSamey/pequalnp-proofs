"""Independent exhaustive subspace and local layer optima for all tiny graphs."""
from itertools import combinations,product


def all_spaces(d):
    for k in range(d+1):
        for piv in combinations(range(d),k):
            free=[(i,b) for i,p in enumerate(piv) for b in range(p+1,d) if b not in piv]
            for code in range(1<<len(free)):
                rows=[1<<p for p in piv]
                for j,(i,b) in enumerate(free):
                    if code>>j & 1:
                        rows[i]|=1<<b
                span=[0]
                for row in rows:
                    span += [x^row for x in span]
                yield k,sum(1<<v for v in span)


def plane(a,b):
    return (1<<a)|(1<<b)|(1<<(a^b))


def main():
    full=local=0
    for n in range(1,5):
        all_edges=list(combinations(range(n),2))
        directions=[[x<<(2*v) for x in [1,2,3]] for v in range(n)]
        base=[plane(a,b) for a,b,c in directions]
        eg=[[plane(directions[u][i],directions[v][i]) for i in range(3)] for u,v in all_edges]
        if n<=3:
            spaces=[(k,s) for k,s in all_spaces(2*n) if all(s&p for p in base)]
        for graph in range(1<<len(all_edges)):
            edges=[(u,v) for j,(u,v) in enumerate(all_edges) if graph>>j&1]
            alpha=max(x.bit_count() for x in range(1<<n) if all(not(x>>u & x>>v &1) for u,v in edges))
            if n<=3:
                gates=[p for j,ps in enumerate(eg) if graph>>j&1 for p in ps]
                opt=next(k for k,s in spaces if all(s&p for p in gates))
                assert opt==2*n-alpha
                full+=1
            # Direct-sum W intersects a gate iff it contains at least one
            # endpoint direction, since membership is independent by row.
            cost=min(sum(c==3 for c in choices) for choices in product(range(4),repeat=n)
                     if all(choices[u] in (i,3) or choices[v] in (i,3)
                            for u,v in edges for i in range(3)))
            assert cost==n-alpha
            local+=1
    print(f'{full} arbitrary-subspace optima and {local} promotion optima passed.')


if __name__=='__main__':
    main()
