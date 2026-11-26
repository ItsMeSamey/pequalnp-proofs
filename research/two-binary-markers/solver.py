"""Find a disjoint primal/dual witness for two binary markers."""
from collections import deque

class Basis:
    def __init__(self):
        self.rows = {}

    def reduce(self, value):
        combination = 0
        while value:
            pair = self.rows.get(value.bit_length()-1)
            if pair is None:
                break
            v, w = pair
            value ^= v
            combination ^= w
        return value, combination

    def add(self, value, combination):
        rest, used = self.reduce(value)
        if rest:
            self.rows[rest.bit_length()-1] = rest, used ^ combination
        return not rest, used ^ combination

def marker(weights, mask):
    val = 0
    for i,w in enumerate(weights):
        if mask >> i & 1:
            val ^= w
    return val

def two_terminal(columns,e,f):
    """Return list of real basis indices spanning e and excluding f."""
    if not f:
        return None
    n = len(columns)
    cols = list(columns) + [e,f]
    basis = Basis()
    basis.add(f,1)
    idx = [n+1]
    for i,v in enumerate(columns):
        dep,_ = basis.add(v,1<<len(idx))
        if not dep:
            idx.append(i)
    if basis.reduce(e)[0]:
        return None
    while True:
        basis=Basis()
        for j,i in enumerate(idx):
            basis.add(cols[i],1<<j)
        nonbasic = set(range(n+2)).difference(idx)
        coords = {i:basis.reduce(cols[i])[1] for i in nonbasic}
        if not coords[n]&1:
            return idx[1:]
        adj = [[] for _ in cols]
        for i,mask in coords.items():
            for j,k in enumerate(idx):
                if (mask>>j&1) and (k,i)!=(n+1,n):
                    adj[k].append(i)
                    adj[i].append(k)
        queue=deque([n+1])
        prev={n+1:None}
        while queue and n not in prev:
            v=queue.popleft()
            for w in adj[v]:
                if w not in prev:
                    prev[w]=v
                    queue.append(w)
        if n not in prev:
            return None
        path=[n]
        while prev[path[-1]] is not None:
            path.append(prev[path[-1]])
        path.reverse()
        idx[idx.index(path[2])] = path[1]

def solve(cols,a,b,target):
    """cols are binary integer columns, and a,b are lists of two-bit ints."""
    n=len(cols)
    r=max((x.bit_length() for x in cols),default=0)
    primal,dual,original=Basis(),Basis(),Basis()
    for i,v in enumerate(cols):
        dep,cycle=original.add(v,1<<i)
        if dep:
            primal.add(marker(a,cycle),cycle)
    for row in range(r):
        mask=sum(1<<i for i,v in enumerate(cols) if v>>row&1)
        dual.add(marker(b,mask),mask)
    for image,which in [(primal,0),(dual,1)]:
        rem,mask=image.reduce(target)
        if not rem:
            return (mask,0) if which==0 else (0,mask)
    if len(primal.rows)!=1 or len(dual.rows)!=1:
        return None
    p=next(iter(primal.rows))
    q=next(iter(dual.rows))
    if primal.rows[p][0]^dual.rows[q][0]!=target:
        return None
    ext=[v | (((w>>p)&1)<<r) for v,w in zip(cols,a)]
    f=0
    for v,w in zip(cols,b):
        if w>>q&1:
            f ^= v
    e=1<<r
    X=two_terminal(ext,e,f)
    if X is None:
        return None
    bas=Basis()
    for i in X:
        bas.add(ext[i],1<<i)
    assert bas.reduce(e)[0]==0
    x=bas.reduce(e)[1]
    # Derive a separating functional by recording the coefficient of f
    # in a basis consisting of X, f and extra ambient unit vectors.
    separator=Basis()
    for i in X:
        separator.add(ext[i],0)
    assert not separator.add(f,1)[0]
    for j in range(r+1):
        separator.add(1<<j,0)
    y=sum(1<<i for i,v in enumerate(ext) if separator.reduce(v)[1])
    assert not x&y and marker(a,x)^marker(b,y)==target
    return x,y
