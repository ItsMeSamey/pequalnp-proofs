"""Deterministic cographic search under a bound on projected partition count."""
from sparse_projected import prime_list
from rank_one_grove import BinaryField,evaluate,toggle


def query(n,edges,omega,lam,bound):
    edges=tuple(tuple(e) for e in edges);omega=tuple(tuple(x) for x in omega)
    if n<1 or bound<1 or lam not in (1,2,3):raise ValueError("invalid parameters")
    m=len(edges);q=[0]*n;adj=[set() for _ in range(n)]
    for u,v,t in edges:
        if not(0<=u<n and 0<=v<n and 0<=t<4):raise ValueError("invalid physical site")
        q[u]^=t;q[v]^=t;adj[u].add(v);adj[v].add(u)
    seen={0};queue=[0]
    for u in queue:
        for v in adj[u]-seen:seen.add(v);queue.append(v)
    if len(seen)!=n:raise ValueError("connected graph required")
    H=set()
    for i,j in omega:
        if not 0<=i<j<m:raise ValueError("invalid alternating query")
        for u in edges[i][:2]:
            for v in edges[j][:2]:
                if u!=v:toggle(H,tuple(sorted((u,v))))
    if n<3 or not H:return None
    known=[];primes=prime_list(m*bound*(bound-1)//2+1);fields={}
    def residual(classes,start,field,weights):
        ren={v:j for j,v in enumerate(sorted(set(classes)))};size=len(ren)
        if size<3 or m-start<size-3:return 0
        im=[ren[v] for v in classes];pairs=[(im[u],im[v]) for u,v,t in edges[start:]]
        h=set();ch=set()
        for u,v in H:
            if im[u]!=im[v]:toggle(h,tuple(sorted((im[u],im[v]))))
        for v,c in enumerate(q):
            if (c&lam).bit_count()%2:toggle(ch,im[v])
        total=evaluate(size,pairs,weights[start:],h,ch,im[0],field)
        for partition in known:
            color={}
            for u,c in enumerate(partition):
                if im[u] in color and color[im[u]]!=c:break
                color[im[u]]=c
            else:
                term=1
                for c in range(3):
                    vertices=[i for i in range(size) if color[i]==c];root=vertices.pop()
                    pos={v:k for k,v in enumerate(vertices)}
                    lap=[[0]*len(vertices) for _ in vertices]
                    for (u,v),w in zip(pairs,weights[start:]):
                        if color[u]!=c or color[v]!=c:continue
                        if u!=root:lap[pos[u]][pos[u]]^=w
                        if v!=root:lap[pos[v]][pos[v]]^=w
                        if u!=root and v!=root:lap[pos[u]][pos[v]]^=w;lap[pos[v]][pos[u]]^=w
                    term=field.mul(term,field.det(lap))
                total^=term
        return total
    def point():
        classes=list(range(n))
        for p in primes:
            costs=[(m*p+1)*(i+1)+pow(2,i,p) for i in range(m)]
            degree=(n-3)*max(costs,default=0);k=max(1,degree.bit_length())
            if k not in fields:fields[k]=BinaryField(k)
            field=fields[k]
            for z in range(field.q):
                powers=[z]
                for _ in range(max(costs,default=0).bit_length()):
                    powers.append(field.mul(powers[-1],powers[-1]))
                weights=[]
                for c in costs:
                    w=1
                    while c:
                        low=c&-c;c^=low;w=field.mul(w,powers[low.bit_length()-1])
                    weights.append(w)
                if residual(classes,0,field,weights):return field,weights
        return None
    for _ in range(bound):
        chosen=point()
        if chosen is None:return None
        field,weights=chosen;classes=list(range(n))
        for i,(u,v,t) in enumerate(edges):
            if residual(classes,i+1,field,weights):continue
            a,b=classes[u],classes[v]
            if a==b or not weights[i]:raise AssertionError("invalid include branch")
            classes=[a if v==b else v for v in classes]
        blocks=sorted(set(classes),key=classes.index);index={v:i for i,v in enumerate(blocks)}
        if len(blocks)!=3:raise AssertionError("not a recovered forest")
        partition=tuple(index[v] for v in classes)
        if partition in known:raise AssertionError("repeated partition")
        sums=[0]*3
        for c,v in zip(q,partition):sums[v]^=c
        a,b=(sum(((partition[u]==c)^(partition[v]==c))<<i for i,(u,v,t) in enumerate(edges)) for c in (0,1))
        if not sum((((a>>i)&(b>>j))^((a>>j)&(b>>i)))&1 for i,j in omega)%2:
            raise AssertionError("invalid physical query output")
        if not any(sums):return a,b
        if any((c&lam).bit_count()%2 for c in sums):raise AssertionError("projected charge failed")
        known.append(partition)
    return None
