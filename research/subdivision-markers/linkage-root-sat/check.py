"""Graph-level linkage search and independent exact binary named-kernel checks."""
from collections import Counter
from itertools import combinations, product
from random import Random
from construct import build, named


def elimination(columns):
    pivots={}
    null=[]
    for i,column in enumerate(columns):
        use=1<<i
        while column:
            j=column.bit_length()-1
            if j not in pivots:
                pivots[j]=column,use
                break
            a,b=pivots[j]
            column,use=column^a,use^b
        if not column:
            null.append(use)
    return pivots,null


def ker(edges,roots,X):
    basis,_=elimination((1<<a)^(1<<b) for i,(a,b) in enumerate(edges) if X>>i&1)
    rem=[]
    for v in roots:
        for j,(x,_) in sorted(basis.items(),reverse=True):
            if v>>j&1:
                v^=x
        rem.append(v)
    return elimination(rem)[1]


def equal(A,B):
    rank=lambda x:len(elimination(x)[0])
    return rank(A)==rank(B)==rank(A+B)


def paths(size,edges,pairs):
    adj=[[] for _ in range(size)]
    for i,(a,b) in enumerate(edges):
        adj[a].append((b,i))
        adj[b].append((a,i))
    terminals={v for pair in pairs for v in pair}
    def visit(i,used,mask):
        if i==len(pairs):
            return mask
        s,t=pairs[i]
        banned=used|(terminals-{s,t})
        def grow(v,path,taken):
            if v==t:
                return visit(i+1,used|path,mask|taken)
            for w,e in adj[v]:
                if w in banned or w in path:
                    continue
                result=grow(w,path|{w},taken|(1<<e))
                if result is not None:
                    return result
            return None
        return grow(s,{s},0)
    return visit(0,set(),0)


def validate(size,edges):
    simple={tuple(sorted(e)) for e in edges}
    assert len(simple)==len(edges) and all(a!=b for a,b in edges)
    adj=[[] for _ in range(size)]
    for a,b in edges:
        adj[a].append(b)
        adj[b].append(a)
    assert max(map(len,adj))<=3
    color={0:0}
    stack=[0]
    while stack:
        v=stack.pop()
        for w in adj[v]:
            if w not in color:
                color[w]=1-color[v]
                stack.append(w)
            else:
                assert color[w]!=color[v]
    assert len(color)==size


def partitions(n):
    blocks=[]
    def walk(v):
        if v==n:
            yield tuple(tuple(b) for b in blocks)
            return
        for b in blocks:
            b.append(v)
            yield from walk(v+1)
            b.pop()
        blocks.append([v])
        yield from walk(v+1)
        blocks.pop()
    yield from walk(0)


def test():
    counts=Counter()
    rng=Random(8522)
    cases=[(1,()),(2,((1,),(-1,))), (2,((1,1,1),(-1,-1,-1))),
           (3,((1,-1,1),(2,),(3,-3))), (4,((1,),(-2,),(-3,4)))]
    for flip in product((-1,1),repeat=5):
        cases.append((2,tuple(tuple(v*s for v,s in zip(c,flip[j:])) for j,c in enumerate(((1,2,1),(1,2),(2,),(1,),(2,))))))
    for _ in range(65):
        n=rng.randrange(1,4)
        cls=tuple(tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(1,4))) for _ in range(rng.randrange(2,7)))
        cases.append((n,cls))
    for n,clauses in cases:
        yes=any(all(any(bool(x>>(abs(i)-1)&1)==(i>0) for i in c) for c in clauses) for x in range(1<<n))
        size,edges,pairs=build(n,clauses)
        validate(size,edges)
        X=paths(size,edges,pairs)
        assert (X is not None)==yes
        counts["SAT" if yes else "UNSAT"]+=1
        if yes:
            for mode in ("units","compact","edges"):
                R,K=named(pairs,mode)
                assert equal(K,ker(edges,R,X))
                counts["physical kernels"]+=1
    for k in range(1,5):
        pairs=[(2*i,2*i+1) for i in range(k)]
        E=list(combinations(range(2*k),2))
        for blocks in partitions(2*k):
            X=sum(1<<E.index((group[0],v)) for group in blocks for v in group[1:])
            good=tuple(blocks)==tuple(pairs)
            for mode in ("units","compact","edges"):
                B,K=named(pairs,mode)
                assert equal(K,ker(E,B,X))==good
            counts["all clique partitions"]+=1
    return counts


if __name__=="__main__":
    print(test())
