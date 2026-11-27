"""Check the mod-three port gadget by raw and contracted integer sign sums."""
from itertools import product


def graph_gadget(left,right,edges):
    n=left+right
    assert all(0<=a<left<=b<n for a,b in edges)
    ports=[]
    links=[]
    drift=set()
    base=0
    triples=0
    for v in range(n):
        degree=sum(v in e for e in edges)
        out=degree if v<left else 0
        t=max(1,degree-2)
        if (t+2-degree+out)%2:t+=1
        chain=[list(range(3*i,3*i+3)) for i in range(triples,triples+t)]
        triples+=t
        for j in range(t-1):
            links.append((chain[j].pop(),chain[j+1].pop()))
            base+=1
        ports.append([x for block in chain for x in block])
    for a,b in edges:
        source,target=ports[a].pop(),ports[b].pop()
        links.append((source,target))
        drift.add(source)
        base+=1
    for available in ports:
        for x in available:
            u=3*triples
            triples+=1
            links.extend(((x,u),(u+1,u+2)))
            drift.add(u+1)
    assert sorted(a for link in links for a in link)==list(range(3*triples))
    assert len(set(edges))==len(edges)
    return triples,links,drift,base


def local(s,t,linear_x,linear_y):
    return sum((-1)**((x*y)^(x*linear_x)^(y*linear_y))
               for x in (0,1) if not s or x for y in (0,1) if not t or y)


def contracted(triples,links,drift):
    # Eliminate binary latent variables by integer sum-product; no graph count oracle.
    factors=[((j,),[1,-2]) for j in range(triples)]
    for x,y in links:
        scope=tuple(sorted({x//3,y//3}))
        factors.append((scope,[local(a>>scope.index(x//3)&1,a>>scope.index(y//3)&1,
                                     x in drift,y in drift) for a in range(1<<len(scope))]))
    remaining=set(range(triples))
    while remaining:
        def bag(v):
            return sorted({i for scope,_ in factors if v in scope for i in scope if i!=v})
        v=min(remaining,key=lambda z:(len(bag(z)),z))
        adjacent=[f for f in factors if v in f[0]]
        rest=bag(v)
        factors=[f for f in factors if v not in f[0]]
        new=[]
        for a in range(1<<len(rest)):
            val=0
            for b in (0,1):
                w=1
                for scope,table in adjacent:
                    idx=sum((b if i==v else a>>rest.index(i)&1)<<j for j,i in enumerate(scope))
                    w*=table[idx]
                val+=w
            new.append(val)
        factors.append((tuple(rest),new))
        remaining.remove(v)
    result=1
    for scope,table in factors:
        assert not scope
        result*=table[0]
    return result


def raw(triples,links,drift):
    terms=[7<<(3*j) for j in range(triples)]
    terms.extend(1<<i|1<<j for i,j in links)
    terms.extend(1<<j for j in drift)
    return sum((-1)**(sum(x&t==t for t in terms)%2) for x in range(1<<(3*triples)))


def raw_bitparallel(triples,links,drift):
    # Enumerate raw inputs in high-bit slices; each bit of a word is one low input.
    n=3*triples
    k=min(12,n)
    full=(1<<(1<<k))-1
    cols=[sum((x>>j&1)<<x for x in range(1<<k)) for j in range(k)]
    terms=[7<<(3*j) for j in range(triples)]+[1<<a|1<<b for a,b in links]+[1<<d for d in drift]
    lookup=[]
    for t in terms:
        word=full
        for j in range(k):
            if t>>j&1:word&=cols[j]
        lookup.append((t>>k,word))
    ones=0
    for high in range(1<<(n-k)):
        parity=0
        for needed,col in lookup:
            if high&needed==needed:parity^=col
        ones+=parity.bit_count()
    return (1<<n)-2*ones


def check(left,right,edges):
    m,links,drift,base=graph_gadget(left,right,edges)
    z=contracted(m,links,drift)
    if 3*m<=18:assert z==raw(m,links,drift)
    bis=sum(all(not(x>>a&x>>b&1) for a,b in edges) for x in range(1<<(left+right)))
    assert (z-(-1)**base*bis)%3==0
    return 3*m<=18


if __name__=='__main__':
    # Independently check all four entries of the clean / oriented couplings.
    assert [local(s,t,False,False) for s,t in product((0,1),repeat=2)]==[2,0,0,-1]
    assert [local(s,t,True,False) for s,t in product((0,1),repeat=2)]==[2,2,0,1]
    raw_cases=total=0
    for l,r in ((0,0),(1,0),(0,1),(1,1),(1,2),(2,2),(2,3)):
        possible=[(i,l+j) for i in range(l) for j in range(r)]
        for s in range(1<<len(possible)):
            raw_cases+=check(l,r,[e for j,e in enumerate(possible) if s>>j&1])
            total+=1
    m,links,drift,_=graph_gadget(1,1,[(0,1)])
    assert 3*m==24 and raw_bitparallel(m,links,drift)==contracted(m,links,drift)
    raw_cases+=1
    assert check(1,5,[(0,i) for i in range(1,6)]) is False
    print(total+1,'graphs;',raw_cases,'raw cases; local matching tables passed')
