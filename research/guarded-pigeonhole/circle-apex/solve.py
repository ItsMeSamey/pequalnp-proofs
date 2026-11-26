"""Randomized witness search for a chord word with arbitrary apex attachments."""
from random import SystemRandom
from math import isqrt

def field_prime(size):
    p=max(3,4*size+1)
    while any(p%j==0 for j in range(2,isqrt(p)+1)):p+=1
    return p

def pfaffian(a,p):
    ans=1
    for k in range(0,len(a),2):
        j=next((j for j in range(k+1,len(a)) if a[k][j]%p),None)
        if j is None:return 0
        if j!=k+1:
            a[j],a[k+1]=a[k+1],a[j]
            for row in a:row[j],row[k+1]=row[k+1],row[j]
            ans=-ans
        pivot=a[k][k+1]%p
        ans=ans*pivot%p
        inv=pow(pivot,-1,p)
        for i in range(k+2,len(a)):
            for j in range(i+1,len(a)):
                a[i][j]=(a[i][j]-(a[k][i]*a[k+1][j]-a[k][j]*a[k+1][i])*inv)%p
                a[j][i]=-a[i][j]
    return ans%p

def filtered(vertices,edges,r,target,p):
    idx={v:i for i,v in enumerate(vertices)}
    ans=0
    for ch in range(1<<r):
        m=[[0]*len(vertices) for _ in vertices]
        for u,v,label,value,wire in edges:
            i,j=idx[u],idx[v]
            a=-value if (ch&label).bit_count()%2 else value
            m[i][j]+=a;m[j][i]-=a
        a=pfaffian(m,p)
        ans+= -a if (ch&target).bit_count()%2 else a
    return ans%p

def branch(word,labels,d,r,target,rng):
    n=len(labels);l=2*n
    if not n:return 0 if not target else None
    positions=[[i for i,u in enumerate(word) if u==v] for v in range(n)]
    if any(len(Q)!=2 for Q in positions):raise ValueError('invalid supplied chord word')
    p=field_prime(4*n);edges=[];wirelabels=[0]*l
    for v,(a,b) in enumerate(positions):
        wirelabels[(a-1)%l]^=labels[v];wirelabels[a]^=labels[v]
        plus=[2*a,2*b+((d>>v)&1)]
        minus=[2*a+1,2*b+(1-((d>>v)&1))]
        for i in plus:
            for j in minus:edges.append((i,j,0,rng.randrange(p),None))
    for i in range(l):
        edges.append((2*i+1,2*((i+1)%l),wirelabels[i],rng.randrange(p),i))
    vertices=list(range(4*n))
    if not filtered(vertices,edges,r,target,p):return None
    wires=0
    while edges:
        u,v,label,value,wire=edges[0];rest=edges[1:]
        if filtered(vertices,rest,r,target,p):
            edges=rest
            continue
        if wire is not None:wires|=1<<wire
        target^=label
        vertices=[w for w in vertices if w!=u and w!=v]
        edges=[e for e in rest if e[0] not in (u,v) and e[1] not in (u,v)]
    assert not vertices and not target
    return sum((((wires>>((a-1)%l))^(wires>>a))&1)<<v for v,(a,b) in enumerate(positions))

def solve(word,core_labels,apex_labels,apex_core,apex_adj,t,target,rng=None,repetitions=1):
    """Return (chord mask,apex mask), or None with bounded false-negative error."""
    if rng is None:rng=SystemRandom()
    n=len(core_labels);d=len(apex_labels)
    for J in range(1<<d):
        labels=list(core_labels);shift=0;z=target;r=t
        for j in range(d):
            if not J>>j&1:continue
            z^=apex_labels[j];shift^=apex_core[j]
            if j!=J.bit_length()-1:  # the last active apex row is the sum of the others
                z|=((apex_adj[j]&J).bit_count()%2)<<r
                for i in range(n):
                    if apex_core[j]>>i&1:labels[i]|=1<<r
                r+=1
        for _ in range(repetitions):
            x=branch(word,labels,shift,r,z,rng)
            if x is not None:
                positions=[[a for a,u in enumerate(word) if u==i] for i in range(n)]
                actual=0
                for i,(a,b) in enumerate(positions):
                    if x>>i&1:
                        crossings=sum(1 for j,(c,e) in enumerate(positions)
                                      if x>>j&1 and ((a<c<b)^(a<e<b)))
                        assert (crossings+(shift>>i&1))%2==0
                        actual^=core_labels[i]
                for j in range(d):
                    if J>>j&1:
                        assert ((apex_adj[j]&J).bit_count()+(apex_core[j]&x).bit_count())%2==0
                        actual^=apex_labels[j]
                assert actual==target
                return x,J
    return None
