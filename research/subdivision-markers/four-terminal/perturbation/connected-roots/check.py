"""Independent finite audit for connected-root perturbations and three dual ports."""
from itertools import combinations,product
from random import Random

def span(columns):
    piv={}
    for x in columns:
        while x:
            i=x.bit_length()-1
            if i not in piv:
                piv[i]=x
                break
            x^=piv[i]
    return piv

def has(piv,x):
    while x:
        i=x.bit_length()-1
        if i not in piv: return False
        x^=piv[i]
    return True

def subsets(s):
    x=s
    while True:
        yield x
        if not x: return
        x=(x-1)&s

def dual(cols):
    # A basis for dependencies, used as rows of a dual representation.
    piv={}
    kernel=[]
    for j,c in enumerate(cols):
        x=c; supp=1<<j
        while x:
            r=x.bit_length()-1
            if r not in piv:
                piv[r]=(x,supp); break
            v,k=piv[r]; x^=v; supp^=k
        if not x: kernel.append(supp)
    return [sum((k>>j&1)<<i for i,k in enumerate(kernel)) for j in range(len(cols))]

def moment_dual(n,edges,demands,targets):
    cols=[(1<<u)^(1<<v)^(g<<n) for u,v,g in edges]
    f=1<<n
    raw=dual(cols+[d^(b<<n) for d,b in zip(demands,targets)]+[f])
    m=len(cols)
    p,q,h=raw[m:]
    ports=[p,q,p^q^h]
    allE=(1<<m)-1
    for Y in subsets(allE):
        sub=[v for j,v in enumerate(raw[:m]) if Y>>j&1]+ports
        if not any_xor(sub) and len(span(sub))==len(sub)-1:
            return True
    return False

def any_xor(cols):
    s=0
    for v in cols:s^=v
    return s

def graph_from(n,edges,mask):
    rows=[[] for _ in range(n)]
    for i,(a,b,g) in enumerate(edges):
        if mask>>i&1:
            rows[a].append((b,g,i)); rows[b].append((a,g,i))
    return rows

def reached(rows,s):
    visited={s}; todo=[s]
    for v in todo:
        for w,_,_ in rows[v]:
            if w not in visited:
                visited.add(w);todo.append(w)
    return visited

def moments_tree(n,edges,demands,targets):
    for inds in combinations(range(len(edges)),n-1):
        mask=sum(1<<i for i in inds)
        rows=graph_from(n,edges,mask)
        if len(reached(rows,0))<n:continue
        phi={0:0};todo=[0]
        for v in todo:
            for w,g,_ in rows[v]:
                if w not in phi:
                    phi[w]=phi[v]^g;todo.append(w)
        y=sum(bit<<i for i,bit in phi.items())
        if all((y&d).bit_count()%2==b for d,b in zip(demands,targets)):return True
    return False

def simple_cycle(n,edges,mask):
    if not mask:return False
    rows=graph_from(n,edges,mask)
    vs={i for i,r in enumerate(rows) if r}
    return all(len(rows[i])==2 for i in vs) and reached(rows,min(vs))==vs

def balanced_path_case(n,edges,D,R):
    allE=(1<<len(edges))-1
    A=[(1<<u)^(1<<v)^(D*g) for u,v,g in edges]
    def good(mask):
        cols=[z for i,z in enumerate(A) if mask>>i&1]
        return not any_xor(cols) and len(span(cols))==len(cols)-1
    direct=any(simple_cycle(n,edges,R|X) and not (sum(g for i,(_,_,g) in enumerate(edges)
                if (R|X)>>i&1)%2) and good(R|X) for X in subsets(allE^R))
    rows=graph_from(n,edges,R); S={i for i,r in enumerate(rows) if r}
    assert R and reached(rows,min(S))==S
    leaves=[i for i in S if len(rows[i])==1]
    if len(leaves)!=2 or any(len(rows[i])>2 for i in S):
        prediction=simple_cycle(n,edges,R) and not (sum(g for i,(_,_,g) in enumerate(edges) if R>>i&1)%2) and good(R)
        return direct==prediction
    s,t=leaves
    phi={s:0};todo=[s]
    for v in todo:
        for w,g,_ in rows[v]:
            if w not in phi:
                phi[w]=phi[v]^g;todo.append(w)
    I=S-{s,t}; forbidden=sum(1<<v for v in I)
    rem=[(u,v,g) for i,(u,v,g) in enumerate(edges) if not R>>i&1 and u not in I and v not in I]
    H=graph_from(n,rem,(1<<len(rem))-1)
    W=reached(H,s)
    paths=[]
    def dfs(v,used,score):
        if v==t:
            if score==phi[t]: paths.append(used)
            return
        for w,g,_ in H[v]:
            if not used>>w&1:dfs(w,used|1<<w,score^g)
    dfs(s,1<<s,0)
    if not paths:return not direct
    if D.bit_count()%2 or any(D & ~(P|forbidden) for P in paths):
        return direct
    # Remaining D are guaranteed on every correctly signed closure.
    loc={v:i for i,v in enumerate(sorted(W))}
    rel=[(loc[u],loc[v],g) for u,v,g in rem if u in W]
    d2=(D&~forbidden)^((1<<s)*((D&forbidden).bit_count()%2))
    local_d=sum(1<<loc[v] for v in W if d2>>v&1)
    bs=[phi[t],sum(phi[v] for v in I if D>>v&1)%2]
    ds=[(1<<loc[s])^(1<<loc[t]),local_d]
    return direct==moment_dual(len(W),rel,ds,bs)

if __name__=='__main__':
    rng=Random(919)
    N=0
    for k in range(400):
        n=rng.randrange(1,6)
        edges=[(rng.randrange(i),i,rng.randrange(2)) for i in range(1,n)]
        edges += [(rng.randrange(n),rng.randrange(n),rng.randrange(2)) for i in range(rng.randrange(5))]
        d=[rng.getrandbits(n) for i in range(2)]
        d=[a^(a.bit_count()%2) for a in d]
        for b in product(range(2),repeat=2):
            assert moments_tree(n,edges,d,b)==moment_dual(n,edges,d,b)
            N+=1
    print(N,'two-moment comparisons',flush=True)
    N=0
    for k in range(300):
        n=rng.randrange(2,7)
        edges=[(rng.randrange(i),i,rng.randrange(2)) for i in range(1,n)]
        edges += [(rng.randrange(n),rng.randrange(n),rng.randrange(2)) for i in range(rng.randrange(4))]
        D=rng.randrange(1,1<<n)
        E=(1<<len(edges))-1
        for R in subsets(E):
            if not R or R.bit_count()>4:continue
            rows=graph_from(n,edges,R); S={i for i,r in enumerate(rows) if r}
            if reached(rows,min(S))!=S:continue
            assert balanced_path_case(n,edges,D,R)
            N+=1
    print(N,'connected root/simple-cycle comparisons')
