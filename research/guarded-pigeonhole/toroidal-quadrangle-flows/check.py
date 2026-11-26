"""Compare equivariant extension with direct proper-map enumeration on a periodic tree."""
from collections import deque
from itertools import product
from random import Random

# Axis vertices (i,0), length-four translation, with a two-pronged
# pendant tree at every axis position. The end is increasing i.
def parent(a):
    i,j=a
    return (i+1,0) if not j else (i,0 if j==1 else 1)
def nbr(a):
    i,j=a
    if not j:return {(i-1,0),(i+1,0),(i,1)}
    return {(i,0),(i,2),(i,3)} if j==1 else {(i,1)}
def parity(a):return (a[0]+(a[1]==1))%2
def shift(a,k):return (a[0]+4*k,a[1])
def ball(r):
    S=front={(0,0)}
    for _ in range(r):
        front=set.union(*(nbr(x) for x in front))-S
        S=S|front
    return S

def solve(n,edges,pins):
    B=ball(n)
    dom=[{pins[v]} if v in pins else B.copy() for v in range(n)]
    changed=True
    while changed:
        changed=False
        for u,v,s in edges:
            for a,b,k in ((u,v,s),(v,u,-s)):
                allowed=set()
                for x in dom[b]:
                    t=shift(x,k);allowed.update(nbr(t));allowed.add(t)
                sub=dom[a]&allowed
                if not sub:return False
                if sub!=dom[a]:dom[a]=sub;changed=True
    ys=[]
    for v,d in enumerate(dom):
        top,=[a for a in d if parent(a) not in d]
        ys.append(top if parity(top)==v%2 else parent(top))
    assert all(ys[v]==a for v,a in pins.items())
    assert all(shift(ys[v],s) in nbr(ys[u]) for u,v,s in edges)
    return True

def brute(n,edges,pins):
    vals=[(0,0)]
    def get(v):
        if v==n:return True
        for x in nbr(vals[-1]):
            if v in pins and pins[v]!=x:continue
            if any(shift(x,s) not in nbr(vals[u]) for u,w,s in edges if w==v):continue
            vals.append(x)
            if get(v+1):return True
            vals.pop()
        return False
    return get(1)

def faces():
    for w in product((1,2,3),repeat=4):
        stack=[]
        for z in w:
            if stack and stack[-1]==z:stack.pop()
            else:stack.append(z)
        actual=any(all(len({c[i],w[i],c[(i+1)%4]})==3 for i in range(4))
                   for c in product((1,2,3),repeat=4))
        assert actual==(not stack)

if __name__=='__main__':
    faces()
    R=Random(65637);positive=negative=0
    for _ in range(1800):
        n=R.randrange(3,9);E=[(i,i+1,0) for i in range(n-1)]
        E.extend((i,j,R.choice((-1,0,1))) for i in range(n) for j in range(i+3,n,2)
                 if R.random()<.27)
        pins={0:(0,0)}
        for i in range(1,n):
            if R.random()<.23:
                pins[i]=R.choice(sorted(a for a in ball(i) if parity(a)==i%2))
        ok=solve(n,E,pins)
        assert ok==brute(n,E,pins)
        positive+=ok;negative+=not ok
    print('81 facial words and 1800 shifted tree-extension cases passed;',positive,'YES,',negative,'NO')
