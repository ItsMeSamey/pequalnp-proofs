"""Exhaust the seven local two-block partitions with physical cycle checks."""

def canon(g):
    return tuple(sorted(tuple(sorted(c)) for c in g if c))
def addpart(state,parts):
    g=list(map(set,state))
    for p in parts:
        inds=[i for i,c in enumerate(g) if c&set(p)]
        if sum(len(g[i]&set(p)) for i in inds)>len(inds):return None
        merged=set(p)
        for i in reversed(inds):merged.update(g.pop(i))
        g.append(merged)
    return g
def transfer(states,a,b,n):
    # fixed left sites 0:n, current boundary n:2n. New local sites 2n,2n+1.
    p=[n+a,n+b,2*n,2*n+1]
    res=set()
    for st in states:
        for m in range(1,8):
            s1=[p[i+1] for i in range(3) if (m>>i)&1]
            s2=[v for v in p if v not in s1]
            g=addpart(st,[s1,s2])
            if g is None:continue
            for c in g:c.difference_update(p[:2])
            if not all(g):continue
            for c in g:
                for near,far in zip(p[:2],p[2:]):
                    if far in c:c.remove(far);c.add(near)
            z=canon(g)
            if z in res:res.remove(z)
            else:res.add(z)
    return res
def check():
    n=3
    s={canon([{i,i+n} for i in range(n)])}
    target=canon([{0},{1,2,3},{4,5}])
    rows=[]
    for t in range(6):
        rows.append(frozenset(s))
        print(t, len(s), target in s)
        a,b=[(0,1),(1,2)][t%2]
        s=transfer(s,a,b,n)
    assert rows[3] == rows[5]
    assert target in rows[3]


if __name__=="__main__":
    check()
