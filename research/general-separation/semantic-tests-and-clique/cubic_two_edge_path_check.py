"""Raw and tensor checks for the zero-drift two-edge path port construction."""
from fractions import Fraction
from itertools import product


def build(left,right,edges,X=None):
    n=left+right
    assert len(set(edges))==len(edges) and all(0<=a<left<=b<n for a,b in edges)
    links=[]
    ports={}
    sizes=[]
    unused=[]
    degree=[]
    blocks=0
    for v in range(n):
        out=[e for e in edges if e[0]==v]
        inc=[e for e in edges if e[1]==v]
        d=len(out)+len(inc)
        p=len(out)+2*len(inc)
        u=max(2,3-p) if X is None else X-d
        if X is None:u+=(u+d)%2
        t=p+u-2
        chain=[list(range(3*j,3*j+3)) for j in range(blocks,blocks+t)]
        blocks+=t
        for a,b in zip(chain,chain[1:]):links.append((a.pop(),b.pop()))
        ids=[(e,0) for e in out]+[(e,k) for e in inc for k in (1,2)]
        assert len(ids)<=t and t>=1
        for key,block in zip(ids,chain):ports[key]=block.pop()
        assert sum(map(len,chain))==u
        sizes.append(t);unused.append(u);degree.append(d)
    for e in edges:
        links.extend((ports[e,0],ports[e,j]) for j in (1,2))
    simple=[tuple(sorted((x//3,y//3))) for x,y in links]
    assert len(set(simple))==len(simple) and all(x!=y for x,y in simple)
    adj=[set() for _ in range(3*blocks)]
    for x,y in links:
        adj[x].add(y);adj[y].add(x)
    assert all(len(v)<=2 for v in adj)
    components=[]
    todo=set(range(3*blocks))
    while todo:
        seen=set();stack=[next(iter(todo))]
        while stack:
            v=stack.pop()
            if v not in seen:
                seen.add(v)
                stack.extend(adj[v]-seen)
        assert len(seen)<=3
        todo-=seen
        components.append(sorted(seen))
    return sizes,unused,degree,links,components


def tensor(sizes,links,components):
    n=sum(sizes)
    factors=[((i,),[1,-2]) for i in range(n)]
    for comp in components:
        scope=sorted({x//3 for x in comp})
        active=[(comp.index(x),comp.index(y)) for x,y in links if x in comp]
        table=[]
        for spins in range(1<<len(scope)):
            val=0
            for xs in product((0,1),repeat=len(comp)):
                if all(xs[j] or not(spins>>scope.index(x//3)&1) for j,x in enumerate(comp)):
                    val+=(-1)**sum(xs[i]*xs[j] for i,j in active)
            table.append(val)
        factors.append((tuple(scope),table))
    remaining=set(range(n))
    while remaining:
        def bag(v):return sorted({j for sc,t in factors if v in sc for j in sc if j!=v})
        v=min(remaining,key=lambda j:(len(bag(j)),j))
        scope=bag(v)
        combined=[f for f in factors if v in f[0]]
        factors=[f for f in factors if v not in f[0]]
        table=[]
        for bits in range(1<<len(scope)):
            total=0
            for w in (0,1):
                weight=1
                for sc,tab in combined:
                    idx=sum((w if j==v else bits>>scope.index(j)&1)<<k for k,j in enumerate(sc))
                    weight*=tab[idx]
                total+=weight
            table.append(total)
        factors.append((tuple(scope),table));remaining.remove(v)
    result=1
    for sc,tab in factors:
        assert not sc
        result*=tab[0]
    return result


def verify(l,r,edges,X=None):
    sizes,U,D,links,components=build(l,r,edges,X)
    z=tensor(sizes,links,components)
    n=l+r
    if 3*sum(sizes)<=15:
        terms=[7<<(3*i) for i in range(sum(sizes))]+[1<<x|1<<y for x,y in links]
        assert z==sum((-1)**sum(t&x==t for t in terms) for x in range(1<<(3*sum(sizes))))
    scale=1<<(sum(t-1 for t in sizes)+sum(U)+2*len(edges))
    hist=[0]*(n+1)
    total=Fraction()
    for bits in range(1<<n):
        if any(bits>>a&1 and not bits>>b&1 for a,b in edges):continue
        hist[bits.bit_count()]+=1
        w=Fraction(1)
        for v in range(n):
            if bits>>v&1:w*=-Fraction(2,1<<(U[v]+D[v]))
        total+=w
    assert z==scale*total
    count=sum(all(not(bits>>a&bits>>b&1) for a,b in edges) for bits in range(1<<n))
    assert count==sum(hist)
    if X is None:
        assert z%3==(scale*count)%3
    else:
        radix=1<<(X-1)
        num,rem=divmod(z*radix**n,scale)
        assert rem==0
        for j in range(n,-1,-1):
            digit=num%radix
            if 2*digit>radix:digit-=radix
            assert digit==(-1)**j*hist[j]
            num=(num-digit)//radix
        assert num==0
    return 3*sum(sizes)<=15


if __name__=='__main__':
    local=[sum((-1)**(x*y+y*z) for x,y,z in product((0,1),repeat=3)
               if (not s or y) and (not t or x*z)) for s,t in product((0,1),repeat=2)]
    assert local==[4,2,0,1]
    total=raw=0
    for l,r in ((0,0),(1,0),(0,1),(1,1),(1,2),(2,2)):
        poss=[(a,l+b) for a in range(l) for b in range(r)]
        for mask in range(1<<len(poss)):
            E=[e for i,e in enumerate(poss) if mask>>i&1]
            delta=max((sum(v in e for e in E) for v in range(l+r)),default=0)
            for X in (None,delta+l+r+4):
                raw+=verify(l,r,E,X);total+=1
    print(total,'parameterized graphs;',raw,'raw checks; both exact regimes passed')
