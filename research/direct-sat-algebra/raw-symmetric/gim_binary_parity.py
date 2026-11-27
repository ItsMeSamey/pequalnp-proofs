"""Deterministic GF(2) delta-parity augmentor using explicit blossom paths.

Reference: Geelen, Iwata & Murota (2003), section 5. Vertices 2i,2i+1
are mates. The matrix is binary alternating, packed one row per integer.
"""
from collections import deque
from itertools import combinations
from hidden_product_network import encoder
from quadratic_centroid import independent


def bits(x):
    while x:
        low=x&-x
        yield low.bit_length()-1
        x^=low


def pivot(rows,support):
    """Principal pivot via row operations on a binary [I | A] representation."""
    n=len(rows)
    columns=[rows[i] if support>>i&1 else 1<<i for i in range(n)]
    inverse=encoder(columns)
    return [inverse((1<<i) if support>>i&1 else rows[i]) for i in range(n)]


def search(matrix,F):
    rows=list(matrix)
    n=len(rows)
    originals=list(range(n))
    sources=[i for i in range(n) if ((F>>i)^(F>>(i^1)))&1]
    paths={i:[i] for i in sources}
    group={i:frozenset((i,i^1)) for i in sources}
    seen=[]
    queue=deque(sources)
    time={}
    def neighbor(i,j):
        return (rows[i]>>j)&1
    def transform(p,q):
        # p,q are original tips both adjacent to the bud; binary coefficients are one.
        t=len(rows)
        col=rows[p]^rows[q]
        for i in bits(col):
            rows[i]|=1<<t
        rows.append(col)
        originals.append(p)
        return t
    def label(x,path):
        paths[x]=path
        queue.append(x)
    while queue:
        v=queue.popleft()
        for u in seen:
            if not neighbor(v,u) or u in group[v]:
                continue
            pv,pu=paths[v],paths[u]
            if pv[0]//2!=pu[0]//2:
                path=pv+pu[::-1]
                return sum(1<<originals[i] for i in path)
            b=next(x for x in reversed(pv) if any(y in group[x] for y in pu))
            d=next(y for y in reversed(pu) if y in group[b])
            sv=pv[pv.index(b)+1:]
            su=pu[pu.index(d)+1:]
            if b==d:
                p,q=sv[0],su[0]
                t=transform(p,q)
                group_new={t}
                excluded={p,q}
            else:
                group_new=set(group[b])
                excluded=set()
            inner=(set(sv)|set(su))-excluded
            for x in inner:
                if x in paths:
                    group_new.update(group[x])
            for x in sorted(inner-paths.keys(),key=lambda x:(-time[x],x)):
                if x in su:
                    path=pv+pu[pu.index(x)+1:][::-1]+[x]
                else:
                    path=pu+pv[pv.index(x)+1:][::-1]+[x]
                label(x,path)
            if b==d:
                label(t,pu+pv[pv.index(p)+1:][::-1]+[t])
            g=frozenset(group_new)
            for x in g:
                group[x]=g
        for u in range(n):
            if u in group or not neighbor(v,u):
                continue
            mate=u^1
            time[u]=len(seen)
            if neighbor(v,mate):
                t=transform(mate,u)
                g=frozenset((u,mate,t))
                label(t,paths[v]+[u,t])
            else:
                g=frozenset((u,mate))
                label(mate,paths[v]+[u,mate])
            for x in g:
                group[x]=g
        seen.append(v)
    return None


def solve(rows,twist):
    """Return a feasible union of mate pairs, or None when none exists."""
    n=len(rows)
    if n%2 or not 0<=twist<1<<n or any(v<0 or v>>n for v in rows):
        raise ValueError("invalid parity instance")
    if any(row>>i&1 for i,row in enumerate(rows)) or any(
            ((rows[i]>>j)^(rows[j]>>i))&1 for i,j in combinations(range(n),2)):
        raise ValueError("matrix must be alternating")
    F=twist
    while any(((F>>(2*i))&3) in (1,2) for i in range(n//2)):
        current=pivot(rows,F^twist)
        aug=search(current,F)
        if aug is None:
            return None
        if len(independent(current[i]&aug for i in bits(aug)))!=aug.bit_count():
            raise ArithmeticError("singular augmenting support")
        previous=sum(((F>>(2*i))&3) in (1,2) for i in range(n//2))
        F^=aug
        if sum(((F>>(2*i))&3) in (1,2) for i in range(n//2))!=previous-2:
            raise ArithmeticError("augmentation did not remove two split pairs")
    return F


def profile(W,labels,odd):
    """Return a nonsingular support with exact label-class parities, or None."""
    n=len(W)
    if len(labels)!=n or any(v<0 or v>>n for v in W) or any(
            ((W[i]>>j)^(W[j]>>i))&1 for i,j in combinations(range(n),2)):
        raise ValueError("invalid symmetric principal matrix")
    odd=set(odd)
    if odd-set(labels):
        return None
    dummy=n
    total=n+1
    rows=[0]*(2*total)
    diagonal=sum((W[i]&(1<<i)) for i in range(n))
    # Alternating lift. Even S uses S; odd S uses S plus the dummy.
    for i in range(n):
        row=W[i]^(diagonal if W[i]>>i&1 else 0)
        for j in bits(row):
            rows[2*i]|=1<<(2*j)
        if W[i]>>i&1:
            rows[2*i]|=1<<(2*dummy)
            rows[2*dummy]|=1<<(2*i)
    for i,j in combinations(range(n),2):
        if labels[i]==labels[j]:
            rows[2*i+1]|=1<<(2*j+1)
            rows[2*j+1]|=1<<(2*i+1)
    twist=sum(1<<(2*labels.index(label)+1) for label in odd)
    if len(odd)%2:
        twist|=1<<(2*dummy+1)
    result=solve(rows,twist)
    if result is None:
        return None
    S=sum(((result>>(2*i))&1)<<i for i in range(n))
    if len(independent(W[i]&S for i in bits(S)))!=S.bit_count():
        raise ArithmeticError("principal witness failed")
    if {a for a in set(labels) if sum(labels[i]==a for i in bits(S))%2}!=odd:
        raise ArithmeticError("class parity mismatch")
    return S


def prescribed(W,labels,target):
    """Enumerate only profiles of weight <=2 rank(H), by symmetric proximity."""
    classes=sorted(set(labels)-{0})
    w=len(independent(classes))
    for k in range(min(2*w,len(classes))+1):
        for odd in combinations(classes,k):
            value=0
            for label in odd:
                value^=label
            if value==target:
                for include_zero in ((False,True) if 0 in labels else (False,)):
                    if include_zero and k==2*w:
                        continue
                    S=profile(W,labels,(*odd,0) if include_zero else odd)
                    if S is not None:
                        return S
    return None


def diagonal_completion(D,labels,target):
    """Find t with D+diag(t) invertible and XOR of selected labels = target."""
    n=len(D)
    if len(labels)!=n or any(v<0 or v>>n for v in D) or any(
            ((D[i]>>j)^(D[j]>>i))&1 for i,j in combinations(range(n),2)):
        raise ValueError("invalid symmetric frozen matrix")
    base=0
    A=list(D)
    for i in range(n):
        mask=(1<<(i+1))-1
        if len(independent(row&mask for row in A[:i+1]))!=i+1:
            A[i]^=1<<i
            base^=1<<i
    inverse=encoder(A)
    W=[(1<<i)^inverse(1<<i) for i in range(n)]
    shift=target
    for i in bits(base):
        shift^=labels[i]
    S=prescribed(W,labels,shift)
    if S is None:
        return None
    t=base^S
    check=0
    for i in bits(t):
        check^=labels[i]
    if check!=target or len(independent(row^(t&(1<<i)) for i,row in enumerate(D)))!=n:
        raise ArithmeticError("diagonal completion replay failed")
    return t
