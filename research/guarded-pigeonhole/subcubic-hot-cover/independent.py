from itertools import combinations, product
from random import Random

def toggles(items):
    s=set()
    for i in items:s.symmetric_difference_update({i})
    return s

def walsh(P,n):
    while True:
        uv=next((m for m in P if m.bit_count()==2),None)
        if uv is None:
            return 0 if any(P) else (-1 if 0 in P else 1)*(1<<n)
        u=uv&-uv; v=uv^u
        # Sum (-1)^(xy+xR+yS+Q) over x,y to get 2*(-1)^(Q+RS).
        R=[m^u for m in P if m&u and m!=uv]
        S=[m^v for m in P if m&v and m!=uv]
        P={m for m in P if not m&uv} ^ toggles(a|b for a in R for b in S)
        n-=1  # two variables disappear, with an extra factor of two

def affine(rows,n):
    piv={}
    for m,r in rows:
        while m:
            p=m.bit_length()-1
            if p not in piv:
                piv[p]=m,r;break
            z,b=piv[p];m^=z;r^=b
        else:
            if r:return None
    def lift(x,offset):
        for p,(m,r) in sorted(piv.items()):
            x^=(((m&x).bit_count()&1)^(offset*r))<<p
        return x
    return lift(0,1),[lift(1<<j,0) for j in range(n) if j not in piv]

def solve(N,E,g,t):
    V=range(N); adj=[set() for _ in V]; inc=[0]*N
    for i,(a,b) in enumerate(E):
        adj[a].add(b);adj[b].add(a);inc[a]|=1<<i;inc[b]|=1<<i
    cover=set()
    for a,b in E:
        if len(adj[a])==len(adj[b])==3 and not {a,b}&cover:cover.add(a)
    def score(x):
        z=0
        for v in V:
            if x>>v&1:z^=g[v]
        return z
    ans=set()
    for s in range(min(t,N)+1):
        for I in combinations(V,s):
            if any(adj[a].intersection(I) for a in I):continue
            off=set(I).union(*(adj[a] for a in I))
            nodes=sorted(cover-off)
            opts=[[0]+[a|b for a,b in combinations([1<<i for i in range(len(E)) if inc[v]>>i&1],2)] for v in nodes]
            for states in product(*opts):
                eq=[(m,0) for m in inc]
                disabled=set(off)
                for v,A in zip(nodes,states):
                    for i,(a,b) in enumerate(E):
                        if v not in (a,b):continue
                        eq.append((1<<i,int(bool(A>>i&1))))
                        if A and not A>>i&1:disabled.add(a^b^v)
                for v in disabled:
                    eq.extend((1<<i,0) for i in range(len(E)) if inc[v]>>i&1)
                sol=affine(eq,len(E))
                if sol is None:continue
                base,B=sol; d=len(B)
                def f(e):
                    return score(sum(1<<v for v in V if (e&inc[v]).bit_count()==2))^score(sum(1<<v for v in I))
                c=f(base);lin=[f(base^x)^c for x in B]
                coeff={0:c,**{1<<i:z for i,z in enumerate(lin)}}
                for i,j in combinations(range(d),2):
                    coeff[(1<<i)|(1<<j)]=f(base^B[i]^B[j])^lin[i]^lin[j]^c
                W=[walsh({m for m,x in coeff.items() if (h&x).bit_count()%2},d) for h in range(1<<t)]
                for z in range(1<<t):
                    count=sum(w*(-1)**((h&z).bit_count()%2) for h,w in enumerate(W))
                    assert count>=0 and count%(1<<t)==0
                    if count:ans.add(z)
    real={score(x) for x in range(1<<N) if all(not(x>>v&1) or sum(x>>u&1 for u in adj[v])%2==0 for v in V)}
    assert ans==real,(E,g,t,ans,real)
rng=Random(27182)
for n in range(1,5):
    edges=list(combinations(range(n),2))
    for mask in range(1<<len(edges)):
        E=[e for i,e in enumerate(edges) if mask>>i&1]
        for t in range(3):solve(n,E,[rng.randrange(1<<t) for _ in range(n)],t)
for _ in range(300):
    n=rng.randrange(4,11);P=list(combinations(range(n),2));rng.shuffle(P);E=[];deg=[0]*n
    for a,b in P:
        if max(deg[a],deg[b])<3 and rng.randrange(4)==0:E.append((a,b));deg[a]+=1;deg[b]+=1
    t=rng.randrange(4);solve(n,E,[rng.randrange(1<<t) for _ in range(n)],t)
print('All 525 graph/label instances matched for every target.')
for n in range(5):
    terms=[m for m in range(1<<n) if m.bit_count()<=2]
    for bits in range(1<<len(terms)):
        P={m for j,m in enumerate(terms) if bits>>j&1}
        assert walsh(P,n)==sum((-1)**sum((m&x)==m for m in P) for x in range(1<<n))
print('Quadratic Walsh elimination also matched all polynomials in up to four variables.')
