from itertools import combinations
from math import comb
from common_outside_family import common_outside_family


def connected_on(part, edges):
    reached = {min(part)}
    while True:
        old = reached.copy()
        for a,b in edges:
            if a in reached and b in part:reached.add(b)
            if b in reached and a in part:reached.add(a)
        if old==reached:return reached==part


def check(n, edges, p, degree, cap):
    rows, failed = common_outside_family(n,edges,p,degree,max_core_size=cap)
    assert failed is None and len(rows)==sum(comb(n,i)*(p-1)**i for i in range(degree+1))
    assert all(connected_on({i for i,c in enumerate(row) if c==j},edges)
               for row in rows for j in range(p))
    return len(rows)

if __name__=='__main__':
    clique=list(combinations(range(8),2))
    bip=[(a,b) for a in range(4) for b in range(4,8)]
    assert common_outside_family(8,bip,2,2,max_core_size=1)[0] is None
    assert common_outside_family(5,[(i,i+1) for i in range(4)],2,2)[0] is None
    print('K8 (three colors):',check(8,clique,3,2,1))
    print('K4,4 (two colors):',check(8,bip,2,2,2))
