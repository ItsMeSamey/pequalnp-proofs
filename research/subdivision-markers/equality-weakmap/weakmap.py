"""Equality interpolation when its subfield quotient represents a binary matroid."""
from collections import deque
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).resolve().parents[1]/'binary-aggregate-selector'))
from solver import apply, basis, interpolate, solve

def mul(x,y):
    result=0
    while y:
        if y&1:
            result^=x
        y>>=1
        x<<=1
        if x&16:
            x^=19
    return result

def inverse(x):
    if not x:
        raise ZeroDivisionError
    return next(v for v in range(1,16) if mul(v,x)==1)

subfield=(0,1,6,7)
assert mul(6,6)==7

def binary_scalable(N,r):
    incident=[[] for _ in range(r+len(N))]
    for j,col in enumerate(N):
        for i,b in enumerate(col):
            if b:
                incident[i].append((r+j,b))
                incident[r+j].append((i,b))
    scale={}
    for root in range(len(incident)):
        if root in scale:
            continue
        scale[root]=1
        queue=[root]
        while queue:
            x=queue.pop()
            for y,b in incident[x]:
                val=inverse(mul(scale[x],b))
                if y not in scale:
                    scale[y]=val
                    queue.append(y)
                elif val!=scale[y]:
                    return False
    return True

def change_basis(A,N,B,J):
    r=len(B)
    edges=[[] for _ in range(r+len(J))]
    extras=[]
    for j,col in enumerate(N):
        for i,val in enumerate(col):
            original=(A[j]>>i)&1
            if original and not val:
                return [f for f in B if f!=B[i]]+[J[j]]
            if original:
                edges[i].append(r+j)
            if val:
                edges[r+j].append(i)
                if not original:
                    extras.append((r+j,i))
    best=None
    for tail,head in extras:
        pred={head:None}
        queue=deque([head])
        while queue and tail not in pred:
            x=queue.popleft()
            for y in edges[x]:
                if y not in pred:
                    pred[y]=x
                    queue.append(y)
        if tail not in pred:
            continue
        path=[]
        x=tail
        while x is not None:
            path.append(x)
            x=pred[x]
        if best is None or len(path)<len(best):
            best=path
    if best is None:
        return None
    return [e for i,e in enumerate(B) if i not in best]+[J[j] for j in range(len(J)) if r+j in best]

def local_blocks(A,N,r):
    """Strong components of the oriented support graph."""
    adj=[[] for i in range(r+len(A))]
    rev=[[] for i in adj]
    for j,col in enumerate(N):
        for i,val in enumerate(col):
            if A[j]>>i&1:
                adj[i].append(r+j)
                rev[r+j].append(i)
            if val:
                adj[r+j].append(i)
                rev[i].append(r+j)
    def reach(graph,x):
        seen={x}
        stack=[x]
        while stack:
            x=stack.pop()
            for y in graph[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return seen
    rem=set(range(len(adj)))
    while rem:
        x=next(iter(rem))
        vertices=reach(adj,x)&reach(rev,x)
        rem-=vertices
        yield sorted(v for v in vertices if v<r),sorted(v-r for v in vertices if v>=r)


def attempt(T,o,U,pin):
    """Return (yes, basis), (no, None) or (outside binary class, None)."""
    B=basis(T)
    bs=tuple(T[e] for e in B)
    extra=interpolate(U,pin)
    shifted=tuple(v^apply(extra,t) for t,v in zip(T,o))
    base=interpolate(bs,[shifted[e] for e in B])
    z=[apply(base,u) for u in U]
    p0=subfield[z[0]]^mul(2,subfield[z[1]])
    if not p0:
        return 'yes',B
    J=tuple(e for e in range(len(T)) if e not in B)
    P=[solve(bs,u) for u in U]
    W=[((P[0]>>i)&1)^(2*((P[1]>>i)&1)) for i in range(len(B))]
    A=tuple(solve(bs,T[e]) for e in J)
    N=[]
    for e,a in zip(J,A):
        g=subfield[shifted[e]^apply(base,T[e])]
        weight=mul(g,inverse(p0))
        N.append(tuple(((a>>i)&1)^mul(w,weight) for i,w in enumerate(W)))
    for j,col in enumerate(N):
        for i,b in enumerate(col):
            if A[j]>>i&1 and b==0:
                return 'yes',[e for e in B if e!=B[i]]+[J[j]]
    unresolved=False
    for rows,cols in local_blocks(A,N,len(B)):
        if not rows or not cols:
            continue
        smallA=tuple(sum(((A[j]>>i)&1)<<h for h,i in enumerate(rows)) for j in cols)
        smallN=tuple(tuple(N[j][i] for i in rows) for j in cols)
        if not binary_scalable(smallN,len(rows)):
            unresolved=True
            continue
        new=change_basis(smallA,smallN,[B[i] for i in rows],[J[j] for j in cols])
        if new is not None:
            new.extend(e for i,e in enumerate(B) if i not in rows)
            h=interpolate([T[e] for e in new],[o[e] for e in new])
            assert all(apply(h,u)==v for u,v in zip(U,pin))
            return 'yes',new
    return ('outside binary class' if unresolved else 'no'),None
