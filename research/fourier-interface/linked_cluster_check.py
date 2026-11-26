"""Exact truncated log clusters for Boolean edge factors on small graphs."""
from fractions import Fraction as F
from functools import cache
from itertools import combinations


def submasks(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            break
        sub = (sub-1) & mask


def connected(edges):
    if not edges:
        return False
    reach = set(edges[0])
    while True:
        expanded = reach.union(*(e for e in edges if reach.intersection(e)))
        if expanded==reach:
            return all(reach.issuperset(e) for e in edges)
        reach = expanded


def log(series):
    # (log Z)' Z = Z'
    result = [F(0)]*len(series)
    for i in range(1,len(series)):
        result[i] = series[i] - sum(j*result[j]*series[i-j] for j in range(1,i))/F(i)
    return result


def exp(series):
    result = [F(1)]
    for i in range(1,len(series)):
        result.append(sum(j*series[j]*result[i-j] for j in range(1,i+1))/F(i))
    return result


def check(n,edges,q):
    @cache
    def local_log(mask):
        # Edge expansion on just this cluster; use normalized moments.
        z = [F(0)]*(q+1)
        for s in submasks(mask):
            size = s.bit_count()
            if 2*size<=q:
                verts = {u for i,e in enumerate(edges) if s>>i & 1 for u in e}
                z[2*size] += F((-1)**size,2**len(verts))
        return log(z)

    total = [F(0)]*(q+1)
    vanishing = 0
    for mask in range(1,1<<len(edges)):
        cluster = [F(0)]*(q+1)
        for sub in submasks(mask):
            sign = (-1)**((mask^sub).bit_count())
            cluster = [a+sign*b for a,b in zip(cluster,local_log(sub))]
        assert all(c==0 for c in cluster[:2*mask.bit_count()])
        selected = [e for i,e in enumerate(edges) if mask>>i & 1]
        if not connected(selected):
            assert not any(cluster)
            vanishing += 1
        elif 2*len(selected)<=q:
            total = [a+b for a,b in zip(total,cluster)]
    direct = [F(0)]*(q+1)
    for x in range(1<<n):
        p = [1]+[0]*q
        for a,b in edges:
            if (x>>a)&(x>>b)&1:
                for i in range(q,1,-1):
                    p[i] -= p[i-2]
        direct = [a+F(b,1<<n) for a,b in zip(direct,p)]
    assert exp(total)==direct
    return vanishing


if __name__=='__main__':
    graphs = [((0,1),(2,3)), ((0,1),(1,2),(2,0),(2,3)),
              tuple(combinations(range(4),2)), (), ((0,1),(1,2),(3,4))]
    count = 0
    for edges in graphs:
        for q in (0,1,2,3,4,5,8,12):
            count += check(5,edges,q)
    print('40 graph/order checks;',count,'disconnected support/order checks')
