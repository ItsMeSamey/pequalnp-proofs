"""Full square-grid recognition and signed separator recursion in polynomial space."""
from math import isqrt
from padded_intermediate import _recognize,_basis


def grid_chart(edges,vertices):
    L=isqrt(len(vertices))
    if L<2 or L*L!=len(vertices): return None
    adj={v:set() for v in vertices}
    for u,v in edges:
        adj[u].add(v)
        adj[v].add(u)
    corners=sorted(v for v in vertices if len(adj[v])==2)
    if len(corners)!=4: return None
    def distances(v):
        d={v:0}
        queue=[v]
        for u in queue:
            for w in adj[u]:
                if w not in d:
                    d[w]=d[u]+1
                    queue.append(w)
        return d
    a=distances(corners[0])
    other=next((v for v in corners if a.get(v)==L-1),None)
    if other is None: return None
    b=distances(other)
    chart={}
    for v in vertices:
        if v not in a or v not in b: return None
        delta=a[v]-b[v]+L-1
        x,y=delta//2,a[v]-delta//2
        if delta%2 or not (0<=x<L and 0<=y<L) or (x,y) in chart: return None
        chart[x,y]=v
    for (x,y),v in chart.items():
        expected={chart[p] for p in ((x-1,y),(x+1,y),(x,y-1),(x,y+1)) if p in chart}
        if adj[v]!=expected: return None
    return L,chart


def bound(w,h):
    if w<h: w,h=h,w
    if not h: return 0
    return (1<<h)*(1+bound(w//2,h)+bound(w-w//2-1,h))


def partition(L,chart,factors):
    adj={v:[] for v in chart.values()}
    for u,v in factors:
        adj[u].append(v)
        adj[v].append(u)
    fixed={}
    def visit(x0,x1,y0,y1):
        w,h=x1-x0,y1-y0
        if w==0 or h==0: return 1
        if w>=h:
            mid=x0+w//2
            line=[chart[mid,y] for y in range(y0,y1)]
            left=(x0,mid,y0,y1)
            right=(mid+1,x1,y0,y1)
        else:
            mid=y0+h//2
            line=[chart[x,mid] for x in range(x0,x1)]
            left=(x0,x1,y0,mid)
            right=(x0,x1,mid+1,y1)
        total=0
        for mask in range(1<<len(line)):
            pref=1
            for j,u in enumerate(line):
                fixed[u]=mask>>j&1
                for v in adj[u]:
                    if v in fixed:
                        a,b=sorted((u,v))
                        pref*=factors[a,b][fixed[a]+2*fixed[b]]
            total+=pref*visit(*left)*visit(*right)
            for u in line: del fixed[u]
        return total
    return visit(0,L,0,L)


def count(n,clauses,checks,rhs=0,*,budget):
    clauses=tuple(tuple(c) for c in clauses)
    checks=tuple(checks)
    if budget<0 or not 0<=rhs<1<<len(checks) or any(not 0<=w<1<<len(clauses) for w in checks):
        raise ValueError("invalid budget or parity checks")
    shape=_recognize(n,clauses)
    if shape is None: return None,{'status':'unrecognized'}
    blocks,vertices,unused=shape
    grid=grid_chart(blocks,vertices)
    if grid is None: return None,{'status':'not-square-grid'}
    L,chart=grid
    basis=_basis(checks,rhs)
    if basis is None: return 0,{'status':'inconsistent'}
    bnd=(1<<len(basis))*(bound(L,L)+sum(4*(1<<d) for half in blocks.values() for d,_,_,_ in half))
    stats=dict(side=L,rank=len(basis),bound=bnd)
    if bnd>budget: return None,dict(stats,status='budget')
    total=0
    for char in range(1<<len(basis)):
        mask=sign=0
        for j,(r,b) in enumerate(basis):
            if char>>j&1:
                mask^=r
                sign^=b
        factors={}
        for e,pair in blocks.items():
            edge=[1]*4
            for d,i,pos,triples in pair:
                vals=[0]*4
                active=[s for j,s in triples if mask>>j&1]
                for a in range(1<<d):
                    phase=sum(a&s==s for s in active)&1
                    for spin in range(4):
                        main=(mask>>i&1) and not(a&1) and spin==(0 if pos else 3)
                        vals[spin]+=1-2*(phase^int(main))
                edge=[x*y for x,y in zip(edge,vals)]
            factors[e]=edge
        total+=(1-2*sign)*partition(L,chart,factors)
    val,rem=divmod(total<<unused,1<<len(basis))
    assert not rem and 0<=val<=1<<n
    return val,dict(stats,status='counted')
