"""Deterministic same-forest search given a promised bound on projected support."""
from math import isqrt
from rank_one_grove import BinaryField,evaluate,toggle


def prime_list(count):
    out=[];p=2
    while len(out)<count:
        if all(p%d for d in range(2,isqrt(p)+1)):out.append(p)
        p+=1 if p==2 else 2
    return out


def query(n,edges,omega,lam,bound):
    """lam is promised to have ≤bound eligible projected forests for exact negatives."""
    edges=tuple(tuple(e) for e in edges);omega=tuple(tuple(p) for p in omega)
    if n<1 or lam not in (1,2,3) or bound<1:raise ValueError("invalid input")
    charges=[0]*n;neighbors=[set() for _ in range(n)]
    for u,v,t in edges:
        if not(0<=u<n and 0<=v<n and 0<=t<4):raise ValueError("invalid physical edge")
        charges[u]^=t;charges[v]^=t;neighbors[u].add(v);neighbors[v].add(u)
    seen={0};walk=[0]
    for v in walk:
        for u in neighbors[v]-seen:seen.add(u);walk.append(u)
    if len(seen)!=n:raise ValueError("connected host required")
    H=set()
    for i,j in omega:
        if not 0<=i<j<len(edges):raise ValueError("invalid query")
        for u in edges[i][:2]:
            for v in edges[j][:2]:
                if u!=v:toggle(H,tuple(sorted((u,v))))
    if n<3 or not H:return None
    M=len(edges);primes=prime_list(M*(bound-1)+1);fields={}
    def nonzero(classes,start):
        rename={v:j for j,v in enumerate(sorted(set(classes)))};size=len(rename)
        if size<3 or M-start<size-3:return False
        im=[rename[v] for v in classes];h=set();charged=set()
        for u,v in H:
            if im[u]!=im[v]:toggle(h,tuple(sorted((im[u],im[v]))))
        if not h:return False
        for v,c in enumerate(charges):
            if (c&lam).bit_count()%2:toggle(charged,im[v])
        pairs=[(im[u],im[v]) for u,v,t in edges[start:]]
        if size==3:return bool(evaluate(size,pairs,[0]*len(pairs),h,charged,im[0],BinaryField(1)))
        for p in primes:
            k=max(1,((size-3)*(p-1)).bit_length())
            if k not in fields:fields[k]=BinaryField(k)
            field=fields[k];exponents=[pow(2,i,p) for i in range(start,M)]
            for z in range(field.q):
                powers=[1]
                for _ in range(1,p):powers.append(field.mul(z,powers[-1]))
                if evaluate(size,pairs,[powers[e] for e in exponents],h,charged,im[0],field):
                    return True
        return False
    todo=[(tuple(range(n)),0)];live=0
    while todo:
        classes,start=todo.pop()
        if not nonzero(classes,start):continue
        live+=1
        if live>1+M*bound:return None
        if len(set(classes))==3:
            blocks=sorted(set(classes)-{classes[0]});sums={}
            for v,c in enumerate(charges):sums[classes[v]]=sums.get(classes[v],0)^c
            if not any(sums.values()):
                a,b=[sum(((classes[u]==l)^(classes[v]==l))<<i for i,(u,v,t) in enumerate(edges))
                     for l in blocks]
                if sum((((a>>i)&(b>>j))^((a>>j)&(b>>i)))&1 for i,j in omega)%2:
                    return a,b
            continue
        if start<M:
            u,v,_=edges[start];a,b=classes[u],classes[v]
            todo.append((classes,start+1))
            if a!=b:todo.append((tuple(a if z==b else z for z in classes),start+1))
    return None
