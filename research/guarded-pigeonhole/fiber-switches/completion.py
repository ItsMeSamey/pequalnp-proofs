"""Construct marker-aware bipartite charts using bit-vector GF(2) algebra."""
from itertools import combinations

def dot(a,b):return (a&b).bit_count()%2

def basis(vec):
    D={}
    for v in vec:
        while v and v.bit_length() in D:v^=D[v.bit_length()]
        if v:D[v.bit_length()]=v
    return D

def solve(E):
    D=basis((r<<1)|b for r,b in E)
    if 1 in D:return None
    x=1
    for h,v in sorted(D.items()):
        if dot(v,x):x|=1<<(h-1)
    return x>>1

def kernel(rows,n):
    D=basis(rows);U=[]
    for i in range(n):
        if i+1 in D:continue
        x=1<<i
        for h,r in sorted(D.items()):
            if dot(x,r):x|=1<<(h-1)
        U.append(x)
    return U

def mv(A,x):return sum(dot(a,x)<<i for i,a in enumerate(A))

def row_sum(A,x):
    r=0
    for i,a in enumerate(A):
        if x>>i&1:r^=a
    return r

def local(v,T):
    n=len(T);x=y=0
    for i,(r,s) in enumerate(T):
        z=(v>>i&1)|((v>>(n+i)&1)<<1)
        x|=dot(r,z)<<i;y|=dot(s,z)<<i
    return x|(y<<n)

def compose(T,S):return [(row_sum(s,a),row_sum(s,b)) for (a,b),s in zip(T,S)]

def chart(W,n):
    cols=[sum((v>>i&1)<<j for j,v in enumerate(W)) for i in range(n)]
    D={};T=[]
    for x in cols:
        while x and x.bit_length() in D:x^=D[x.bit_length()]
        if x:D[x.bit_length()]=x
        T.append((1,2) if x else (2,1))
    mask=(1<<n)-1;D={}
    for w in W:
        w=local(w,T)
        while (w&mask).bit_length() in D:w^=D[(w&mask).bit_length()]
        assert w&mask
        D[(w&mask).bit_length()]=w
    A=[]
    for i in range(n):
        w=D[i+1]
        for j in reversed(range(i)):
            if w>>j&1:w^=D[j+1]
        A.append(w>>n)
    return A,T

def css_local(A):
    n=len(A);todo=set(range(n));T=[None]*n
    while todo:
        c=[min(todo)];todo.remove(c[0])
        for u in c:
            take=[v for v in todo if A[u]>>v&1]
            todo.difference_update(take);c.extend(take)
        m=len(c);R=[sum((A[u]>>v&1)<<j for j,v in enumerate(c)) for u in c]
        E=[]
        for i,j in combinations(range(m),2):
            b=R[i]>>j&1
            E.append((((R[i]&R[j])<<m)^(b*((1<<i)|(1<<j))),b))
        x=solve(E)
        if x is None:return None
        for i in range(m):
            z=solve(E+[(1<<(m+i),0)])
            if z is not None:
                x=z;break
        for i,u in enumerate(c):
            p=x>>i&1;q=x>>(m+i)&1;r=dot(R[i],x>>m);s=1^p
            if (p*s)^(q*r):return None
            def image(v):return dot(p|(q<<1),v)|(dot(r|(s<<1),v)<<1)
            one=next(v for v in (1,2,3) if image(v)==v)
            zero=next(v for v in (1,2,3) if image(v)==0)
            T[u]=(next(v for v in (1,2,3) if dot(v,one) and not dot(v,zero)),
                  next(v for v in (1,2,3) if dot(v,zero) and not dot(v,one)))
    return T

def bip(A):
    colors={}
    for start in range(len(A)):
        if start in colors:continue
        q=[start];colors[start]=0
        for u in q:
            for v in range(len(A)):
                if not A[u]>>v&1:continue
                if v not in colors:colors[v]=1-colors[u];q.append(v)
                elif colors[v]==colors[u]:return False
    return True

def css_transform(W,n):
    A,T=chart(W,n)
    shear=[(1,3 if row>>i&1 else 2) for i,row in enumerate(A)]
    T=compose(shear,T)
    A=[row&~(1<<i) for i,row in enumerate(A)]
    E=css_local(A)
    if E is None:return None
    T=compose(E,T)
    B,S=chart([local(v,T) for v in W],n)
    assert bip(B)
    return B,compose(S,T)

def planes(t,z):
    mask=(1<<t)-1
    cand=[v for v in range(1,1<<(2*t)) if not dot((v&mask)^z,v>>t)]
    spaces={frozenset([0])}
    for _ in range(t):
        more=set()
        for U in spaces:
            for v in cand:
                if v in U or any(dot(v&mask,u>>t)^dot(u&mask,v>>t) for u in U):continue
                more.add(U|{u^v for u in U})
        spaces=more
    return sorted(spaces,key=lambda s:sorted(s))

def recognize(A,L,z):
    """Return (B,Lnew,znew,T) or None; input marker rows must be independent."""
    n=len(A);t=len(L);mask=(1<<n)-1;m=(1<<t)-1
    if len(basis(L))!=t:raise ValueError('expected independent marker rows')
    def embed(x):return x|(mv(A,x)<<n)
    U=[embed(x) for x in kernel(L,n)]
    a=[embed(solve([(r,int(i==j)) for j,r in enumerate(L)])) for i in range(t)]
    b=[r<<n for r in L];w=row_sum(a,z)
    for plane in planes(t,z):
        W=U+[row_sum(a,v&m)^row_sum(b,v>>t) for v in basis(plane).values()]
        result=css_transform(W,n)
        if result is None:continue
        B,T=result
        ones=(1<<(2*n))-1
        base=(local(w^ones,T)^ones)&mask
        rows=kernel([local(v,T)&mask for v in U],n)
        assert len(rows)==t
        return B,rows,mv(rows,base),T
    return None
