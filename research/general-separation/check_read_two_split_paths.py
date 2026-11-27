"""Weighted multilinear extension of signed CNF; signed one-based literals."""
from fractions import Fraction
from itertools import product, permutations
from math import prod


def interpolate(weights, clauses):
    unary = [[1-w,w] for w in weights]
    binary = {}
    reads = [0]*len(weights)
    empty = False
    for c in clauses:
        if len(c)>2:
            raise ValueError("clause width")
        for lit in c:
            if not 1<=abs(lit)<=len(weights):
                raise ValueError("variable index")
            reads[abs(lit)-1]+=1
        if not c:
            empty=True
            continue
        a,b=sorted((c[0],c[-1]),key=abs)
        i,j=abs(a)-1,abs(b)-1
        if i==j:
            for x in (0,1):
                if all((l>0)!=x for l in c):
                    unary[i][x]=0
        else:
            table=binary.setdefault((i,j),[[1,1],[1,1]])
            table[int(a<0)][int(b<0)]=0
    if max(reads,default=0)>2:
        raise ValueError("read limit")
    if empty:
        return 0
    adj=[set() for _ in weights]
    for i,j in binary:
        adj[i].add(j)
        adj[j].add(i)
    def edge(i,j,x,y):
        return binary[i,j][x][y] if i<j else binary[j,i][y][x]
    unseen=set(range(len(weights)))
    answer=1
    for start in sorted(unseen,key=lambda v:len(adj[v])):
        if start not in unseen:
            continue
        path=[start]
        unseen.remove(start)
        while choices:=adj[path[-1]] & unseen:
            v=min(choices)
            path.append(v)
            unseen.remove(v)
        cycle=len(path)>2 and start in adj[path[-1]]
        total=0
        for first in (0,1):
            dp=[0,0]
            dp[first]=unary[start][first]
            for u,v in zip(path,path[1:]):
                dp=[unary[v][y]*sum(dp[x]*edge(u,v,x,y) for x in (0,1)) for y in (0,1)]
            total+=sum(dp[x]*(edge(path[-1],start,x,first) if cycle else 1) for x in (0,1))
        answer*=total
    return answer


def extensions(n):
    adj={}
    def link(v,w,mark=None):
        adj.setdefault(v,[]).append((w,mark))
        adj.setdefault(w,[]).append((v,mark))
    for block in range(2*n):
        for j in range(2*n-2):
            link((block,j),(block,j+1))
    for i,j in product(range(n),repeat=2):
        link((i,2*j),(n+j,2*i),(i,j))
    assert max(map(len,adj.values()))<=3
    def visit(free,chosen):
        if not free:
            yield tuple(sorted(chosen))
            return
        v=min(free)
        for w,mark in adj[v]:
            if w in free:
                yield from visit(free-{v,w},chosen+([] if mark is None else [mark]))
    return list(visit(set(adj),[]))


def main():
    weights=[Fraction(-1,2),Fraction(3,2),Fraction(2,3),Fraction(1,4),2]
    for clauses in [[],[()],[(1,)],[(1,-1)],[(2,2)],[(1,-2),(-1,2)],
                    [(-1,2),(2,3),(-3,4)],[(1,2),(-2,-3),(3,-1),(4,),(-5,)]]:
        expected=sum(prod(w if bit else 1-w for bit,w in zip(bits,weights))
                     for bits in product(range(2),repeat=len(weights))
                     if all(any(bits[abs(l)-1]==(l>0) for l in c) for c in clauses))
        assert interpolate(weights,clauses)==expected
    for n in (2,3):
        matches=extensions(n)
        assert sorted(matches)==sorted(tuple(enumerate(p)) for p in permutations(range(n)))
        def cost(i,j):
            return (-1)**(i+j+i*j)*(2+i+3*j)
        expected=sum(prod(cost(i,p[i]) for i in range(n)) for p in permutations(range(n)))
        assert sum(prod(cost(i,j) for i,j in m) for m in matches)==expected
    print('Signed cube interpolation and sparse matching extensions passed.')


if __name__=='__main__':
    main()
